#![allow(clippy::too_many_arguments)]

use dusk_plonk::constraint_system::StandardComposer;
use dusk_plonk::constraint_system::Variable;
use dusk_plonk::plookup::PlookupTable4Arity;
use dusk_bls12_381::BlsScalar;
use std::io;
use std::io::Write;
use std::convert::TryInto;
use std::vec::Vec;

/// Generates plookup table with nibble-wise XOR table,
/// 3-bit range table, and 2-bit range table
pub fn generate_blake_table() -> PlookupTable4Arity {
    let mut lookup_table = PlookupTable4Arity::new();
    // (3*2^4)^2 = 2304 row nibble-wise XOR table
    // accomodates XOR between sums of up to 3 4-bit numbers
    for i in 0..48u16 {
        for j in 0..48u16 {
            lookup_table.0.push([
                BlsScalar::from(i as u64),
                BlsScalar::from(j as u64),
                BlsScalar::from((i ^ j) as u64),
                BlsScalar::one(),
            ]);
        }
    }
    // 2^4 row 4-bit range table
    for i in 0..2u16.pow(4) {
        lookup_table.0.push([
            BlsScalar::from(i as u64),
            BlsScalar::zero(),
            BlsScalar::zero(),
            BlsScalar::from(2),
        ]);
    }
    // 2^3 row 3-bit range table
    for i in 0..2u16.pow(3) {
        lookup_table.0.push([
            BlsScalar::from(i as u64),
            BlsScalar::zero(),
            BlsScalar::zero(),
            BlsScalar::from(3),
        ]);
    }
    // 2^2 row 2-bit range table
    for i in 0..2u16.pow(2) {
        lookup_table.0.push([
            BlsScalar::from(i as u64),
            BlsScalar::zero(),
            BlsScalar::zero(),
            BlsScalar::from(4),
        ]);
    }

    // 2^9 row nibble-wise ADD table
    for i in 0..2u16.pow(5) {
        for j in 0..2u16.pow(4) {
            lookup_table.0.push([
                BlsScalar::from(i as u64),
                BlsScalar::from(j as u64),
                BlsScalar::from((i + j) as u64),
                BlsScalar::from(5),
            ]);
        }
    }

    lookup_table
}

pub struct Blake2s {
    cs: StandardComposer,
}

impl Blake2s {
    /// Creates a single 256-bit scalar variable from 64 nibble variables 
    pub fn compose_scalar_from_le_nibbles(&mut self, nibbles: &[Variable]) -> Variable {
        // Checks if bytes.len() is a power of two
        assert_eq!(nibbles.len(), 64);

        // compose 32-bit words from 8 range-checked nibbles
        let mut words = [self.cs.zero_var(); 8];
        for i in 0..8 {
            words[i] = self.compose_word_from_le_nibbles(&nibbles[8*i..8*(i+1)]);
        }

        // compose 8-byte octs
        let mut octs = [self.cs.zero_var(); 4];
        for i in 0..4 {
            octs[i] = self.cs.add(
                (BlsScalar::from(1 << 32), words[2*i+1]),
                (BlsScalar::one(), words[2*i]),
                BlsScalar::zero(),
                Some(BlsScalar::zero()),
            );
        }

        // compose 16-byte hexes
        let mut hexes = [self.cs.zero_var(); 2];
        for i in 0..2 {
            hexes[i] = self.cs.add(
                (BlsScalar::from_raw([0,1,0,0]), octs[2*i+1]),
                (BlsScalar::one(), octs[2*i]),
                BlsScalar::zero(),
                Some(BlsScalar::zero()),
            );
        }

        // compose 32-byte/256-bit scalar
        self.cs.add(
            (BlsScalar::from_raw([0,0,1,0]), hexes[1]),
            (BlsScalar::one(), hexes[0]),
            BlsScalar::zero(),
            Some(BlsScalar::zero()),
        )
    }

    /// Creates a variable y = x0*2^(8*3) + x1*2^(8*2) + x2*2^(8*1) + x3
    /// such that if x0..x3 are nibbles, then y is the 32-bit concatenation
    /// x0|x1|x2|x3. 
    pub fn compose_word_from_le_nibbles(&mut self, nibbles: &[Variable]) -> Variable {
        assert_eq!(nibbles.len(), 8);

        // Prove 4 pieces of word are actually nibbles by looking them up in the nibble-sized lookup table
        // If (A, B, A^B) is in the lookup table, then A and B are both less than 2^4

        let nibble_7_xor_nibble_6_var = self.cs.add_input(
            BlsScalar::from(
                self.cs.variables[&nibbles[7]].reduce().0[0] ^ self.cs.variables[&nibbles[6]].reduce().0[0]
            )
        );

        let nibble_5_xor_nibble_4_var = self.cs.add_input(
            BlsScalar::from(
                self.cs.variables[&nibbles[5]].reduce().0[0] ^ self.cs.variables[&nibbles[4]].reduce().0[0]
            )
        );

        let nibble_3_xor_nibble_2_var = self.cs.add_input(
            BlsScalar::from(
                self.cs.variables[&nibbles[3]].reduce().0[0] ^ self.cs.variables[&nibbles[2]].reduce().0[0]
            )
        );

        let nibble_1_xor_nibble_0_var = self.cs.add_input(
            BlsScalar::from(
                self.cs.variables[&nibbles[1]].reduce().0[0] ^ self.cs.variables[&nibbles[0]].reduce().0[0]
            )
        );

        // Ensure all 8 nibbles are < 2^4 using the XOR subtable
        let one_var = self.cs.add_input(BlsScalar::one());
        self.cs.plookup_gate(nibbles[7], nibbles[6], nibble_7_xor_nibble_6_var, Some(one_var), BlsScalar::zero());
        self.cs.plookup_gate(nibbles[5], nibbles[4], nibble_5_xor_nibble_4_var, Some(one_var), BlsScalar::zero());
        self.cs.plookup_gate(nibbles[3], nibbles[2], nibble_3_xor_nibble_2_var, Some(one_var), BlsScalar::zero());
        self.cs.plookup_gate(nibbles[1], nibbles[0], nibble_1_xor_nibble_0_var, Some(one_var), BlsScalar::zero());

        let pair_3 = self.cs.add(
            (BlsScalar::from(1 << 4), nibbles[7]),
            (BlsScalar::one(), nibbles[6]),
            BlsScalar::zero(),
            Some(BlsScalar::zero()),
        );

        let pair_2 = self.cs.add(
            (BlsScalar::from(1 << 4), nibbles[5]),
            (BlsScalar::one(), nibbles[4]),
            BlsScalar::zero(),
            Some(BlsScalar::zero()),
        );

        let pair_1 = self.cs.add(
            (BlsScalar::from(1 << 4), nibbles[3]),
            (BlsScalar::one(), nibbles[2]),
            BlsScalar::zero(),
            Some(BlsScalar::zero()),
        );

        let pair_0 = self.cs.add(
            (BlsScalar::from(1 << 4), nibbles[1]),
            (BlsScalar::one(), nibbles[0]),
            BlsScalar::zero(),
            Some(BlsScalar::zero()),
        );

        let quad_hi = self.cs.add(
            (BlsScalar::from(1 << 8), pair_3),
            (BlsScalar::one(), pair_2),
            BlsScalar::zero(),
            Some(BlsScalar::zero()),
        );

        let quad_lo = self.cs.add(
            (BlsScalar::from(1 << 8), pair_1),
            (BlsScalar::one(), pair_0),
            BlsScalar::zero(),
            Some(BlsScalar::zero()),
        );

        let res = self.cs.add(
            (BlsScalar::from(1 << 16), quad_hi),
            (BlsScalar::one(), quad_lo),
            BlsScalar::zero(),
            Some(BlsScalar::zero()),
        );

        res
        
    }

    /// Modular division by 2^32
    pub fn mod_u32(&mut self, d: Variable) -> Variable {
        // Get u64 value of dividend
        let dividend = self.cs.variables[&d].reduce().0[0];

        // Compute quotient and add as variable
        let quotient = dividend / 2_u64.pow(32);
        let quotient_var = self.cs.add_input(BlsScalar::from(quotient));

        // dividend = quotient * 2^32 + remainder
        // each dividend comes from the sum of two or three
        // u32 words, and thus should be less than 4 (2 bits)
        let four_var = self.cs.add_input(BlsScalar::from(4));
        self.cs.plookup_gate(quotient_var, self.cs.zero_var(), self.cs.zero_var(), Some(four_var), BlsScalar::zero());

        // Show mod has been done correctly with a single add gate
        // which returns the variable holding the remainder
        self.cs.add(
            (BlsScalar::one(), d),
            (-BlsScalar::from(2_u64.pow(32)), quotient_var),
            BlsScalar::zero(),
            Some(BlsScalar::zero()),
        )
    }

    fn word_to_le_nibbles(word_input: u32)-> [u8; 8] {
        let mut word = word_input;
        let mut word_nibbles = [0u8; 8];
        for i in 0..8 {
            word_nibbles[i] = (word % 16) as u8;
            word >>= 4;
        }
        word_nibbles
    }

    /// Decomposes a variable d into 8 nibbles d0..d7 so that
    /// d = d0|d1|..|d7 and adds the required gates showing decomposition is correct
    pub fn decompose_word_into_le_nibbles(&mut self, word: Variable) -> [Variable; 8] {
        let word_value = self.cs.variables[&word].reduce().0[0];
        let word_nibbles = Blake2s::word_to_le_nibbles(word_value as u32);

        let mut word_vars = [self.cs.zero_var(); 8];
        // create variables for each nibbles
        for i in 0..8 {
            word_vars[i] = self.cs.add_input(BlsScalar::from(word_nibbles[i] as u64));
        }
       
        // show bytes compose to input word
        self.compose_word_from_le_nibbles(&word_vars);

        word_vars
    }
    
    /// Adds three variables by adding nibble-by-nibble with plookup, composing the nibbles, and modding
    /// by 2**32
    pub fn add_three_mod_2_32(&mut self, v: &mut [Variable; 128], a: usize, b: usize, x: &[Variable]) {
        let mut sums = [self.cs.zero_var(); 8];
        let mut sum_1 = [self.cs.zero_var(); 8];
        let five_var = self.cs.add_input(BlsScalar::from(5));
        for i in 0..8 {
            let sum_1_var = self.cs.add_input(
                BlsScalar::from(
                    self.cs.variables[&v[8*a+i]].reduce().0[0] +
                    self.cs.variables[&v[8*b+i]].reduce().0[0]
                )
            );
            sum_1[i] = self.cs.plookup_gate(
                v[8*a+i],
                v[8*b+i],
                sum_1_var,
                Some(five_var),
                BlsScalar::zero()
            );
            let sum_var = self.cs.add_input(
                BlsScalar::from(
                    self.cs.variables[&sum_1[i]].reduce().0[0] +
                    self.cs.variables[&x[i]].reduce().0[0]
                )
            );
            sums[i] = self.cs.plookup_gate(
                sum_1[i],
                x[i],
                sum_var,
                Some(five_var),
                BlsScalar::zero()
            );
        }

        let sum = self.compose_word_from_le_nibbles(&sums);

        // compute the remainder mod 2^32
        let remainder = self.mod_u32(sum);

        // decompose remainder back into bytes and add
        // gates showing decomposition is correct
        let decomposed_nibbles = self.decompose_word_into_le_nibbles(remainder);
        v[8*a] = decomposed_nibbles[0];
        v[8*a+1] = decomposed_nibbles[1];
        v[8*a+2] = decomposed_nibbles[2];
        v[8*a+3] = decomposed_nibbles[3];
        v[8*a+4] = decomposed_nibbles[4];
        v[8*a+5] = decomposed_nibbles[5];
        v[8*a+6] = decomposed_nibbles[6];
        v[8*a+7] = decomposed_nibbles[7];
    }

    /// Adds two variables by adding nibble_by_nibble, composing the nibbles, and modding
    /// by 2**32
    pub fn add_two_mod_2_32(&mut self, v: &mut [Variable; 128], c: usize, d: usize) {
        let mut sums = [self.cs.zero_var(); 8];
        let five_var = self.cs.add_input(BlsScalar::from(5));
        for i in 0..8 {
            let sum_var = self.cs.add_input(
                BlsScalar::from(
                    self.cs.variables[&v[8*c+i]].reduce().0[0] +
                    self.cs.variables[&v[8*d+i]].reduce().0[0]
                )
            );
            sums[i] = self.cs.plookup_gate(
                v[8*c+i],
                v[8*d+i],
                sum_var,
                Some(five_var),
                BlsScalar::zero()
            );
        }

        let sum = self.compose_word_from_le_nibbles(&sums);

        // compute the remainder mod 2^32
        let remainder = self.mod_u32(sum);

        // decompose remainder back into bytes and add
        // gates showing decomposition is correct
        let decomposed_nibbles = self.decompose_word_into_le_nibbles(remainder);

        v[8*c] = decomposed_nibbles[0];
        v[8*c+1] = decomposed_nibbles[1];
        v[8*c+2] = decomposed_nibbles[2];
        v[8*c+3] = decomposed_nibbles[3];
        v[8*c+4] = decomposed_nibbles[4];
        v[8*c+5] = decomposed_nibbles[5];
        v[8*c+6] = decomposed_nibbles[6];
        v[8*c+7] = decomposed_nibbles[7];
    }

    /// Rotates to the right by 16 bits by shuffling variables in the working vector
    fn rotate_16(&mut self, v: &mut [Variable; 128], n: usize) {
        // rotate bytes to the right 2 so that v[n+2] := v[n] etc. 
        let mut initial = [self.cs.zero_var(); 8];
        initial.clone_from_slice(&v[8*n..(8*n+8)]);
        for i in 0..8 {
            v[8*n+(i+4)%8] = initial[i]; 
        }
    }

    /// Rotates to the right by 8 bits by shuffling variables in the working vector
    fn rotate_8(&mut self, v: &mut [Variable; 128], n: usize) {
        // rotate nibbles to the right 2 so that v[n-2] := v[n] etc.
        let mut initial = [self.cs.zero_var(); 8];
        initial.clone_from_slice(&v[8*n..(8*n+8)]);
        for i in 0..8 {
            v[8*n+(i+6)%8] = initial[i]; 
        }
    }

    /// Rotates to the right by 12 bits by shuffling variables in the working vector
    fn rotate_12(&mut self, v: &mut [Variable; 128], n: usize) {
        // rotate nibbles to the right 1 so that v[n-3] := v[n] etc.
        let mut initial = [self.cs.zero_var(); 8];
        initial.clone_from_slice(&v[8*n..(8*n+8)]);
        for i in 0..8 {
            v[8*n+(i+5)%8] = initial[i]; 
        }
    }

    /// Rotates to the right by 7 bits by spltting each nibble into pieces and recomposing
    fn rotate_7(&mut self, v: &mut [Variable; 128], n: usize) {
        
        // first split each nibble into 3 high bits and 1 low bit
        let mut split_nibbles = [self.cs.zero_var(); 16];
        for i in (0..8).rev() {
            let current_nibble = self.cs.variables[&v[8*n+i]].reduce().0[0];
            // 1 high bit
            let hi = current_nibble >> 3;
            // 3 low bits
            let lo = current_nibble % (1 << 3);

            // high bits are on even indices, low bits are on odd indices
            split_nibbles[2*i] = self.cs.add_input(BlsScalar::from(hi));
            split_nibbles[2*i+1] = self.cs.add_input(BlsScalar::from(lo));

            // show that the hi bit is actually a bit
            self.cs.boolean_gate(split_nibbles[2*i]);

            // show that the lo bits l are less than 2^3 using subtable 3
            let three_var = self.cs.add_input(BlsScalar::from(3));
            self.cs.plookup_gate(split_nibbles[2*i+1], self.cs.zero_var(), self.cs.zero_var(), Some(three_var), BlsScalar::zero());
        }

        // Now recompose the 8 pairs of high and low bits into 8 nibbles, shifting 
        // shifting 3 space to the right, so that the new first nibble is lo|hi, 
        // using the low bits at index 5 and the high bit at index 2.
        // We do not need to range check the resulting byte since we already
        // checked the two pieces of each nibble
        for i in 0..8 {
            v[8*n+i] =  self.cs.add(
                // 3 low bits become new high bits
                (BlsScalar::from(2), split_nibbles[(2*i+5)%16]),
                // 1 high bit becomes new low bit
                (BlsScalar::one(), split_nibbles[(2*i+2)%16]),
                BlsScalar::zero(),
                Some(BlsScalar::zero()),
            );
        }
    }

    /// Performs a bit rotation right by 16, 12, 8, or 7 bits on the nth word
    pub fn rotate(&mut self, v: &mut [Variable; 128], n: usize, r: usize) {
        match r {
            16 => Blake2s::rotate_16(self, v, n),
            12 => Blake2s::rotate_12(self, v, n),
            8 => Blake2s::rotate_8(self, v, n),
            7 => Blake2s::rotate_7(self, v, n),
            _ => panic!("Not a valid rotation constant for blake2s"),
        };
    }

    /// Performs a nibble-by-nibble XOR of two words given their indices in the working vector
    pub fn xor_by_indices(&mut self, v: &mut [Variable; 128], d: usize, a: usize) {
        // v[d] := (v[d] ^ v[a])
        let mut right = [self.cs.zero_var(); 8];
        right.clone_from_slice(&v[8*a..(8*a+8)]);
        self.xor(&mut v[8*d..(8*d+8)], &right);
    }

    /// Performs an XOR in place, mutating the left inputs
    pub fn xor(&mut self, left: &mut [Variable], right: &[Variable]) {
        assert_eq!(left.len(), right.len());
        // left := left ^ right
        for i in 0..left.len() {
            let left_val = self.cs.variables[&left[i]].reduce().0[0];
            let right_val = self.cs.variables[&right[i]].reduce().0[0];
            let out_var = self.cs.add_input(BlsScalar::from(left_val ^ right_val));
            let one_var = self.cs.add_input(BlsScalar::one());

            left[i] = self.cs.plookup_gate(left[i], right[i], out_var, Some(one_var), BlsScalar::zero());
        }
    }

    /// This function mixes two input words, "x" and "y", into
    /// four words indexed by "a", "b", "c", and "d" selected 
    /// from the working vector v. The 32-bit words in v have
    /// been decomposed into 4 bytes.
    fn mixing (&mut self, v: &mut [Variable; 128], a: usize, b: usize, c: usize, d: usize, x: &[Variable], y: &[Variable]) {
        // line 1: 15 gates
        // v[a] := (v[a] + v[b] + x) mod 2**32
        self.add_three_mod_2_32(v, a, b, x);

        // line 2: 4 gates
        // v[d] := (v[d] ^ v[a]) >>> 16
        self.xor_by_indices(v, d, a);
        self.rotate(v, d, 16);

        // line 3: 11 gates
        // v[c] := (v[c] + v[d]) mod 2**32
        self.add_two_mod_2_32(v, c, d);

        // line 4: 8 gates
        // v[b] := (v[b] ^ v[c]) >>> 12 
        self.xor_by_indices(v, b, c);
        self.rotate(v, b, 12);

        // line 5: 15 gates
        // v[a] := (v[a] + v[b] + y) mod 2**32
        self.add_three_mod_2_32(v, a, b, y);

        // line 6: 4 gates
        // v[d] := (v[d] ^ v[a]) >>> 8
        self.xor_by_indices(v, d, a);
        self.rotate(v, d, 8);

        // line 7: 11 gates
        // v[c] := (v[c] + v[d]) mod 2**32
        self.add_two_mod_2_32(v, c, d);

        // line 8: 8 gates
        // v[b] := (v[b] ^ v[c]) >>> 7 
        self.xor_by_indices(v, b, c);
        self.rotate(v, b, 7);

    }

    /// Generate initial values from fractional part of the square root
    /// of the first 8 primes
    pub fn generate_iv(&mut self) -> [Variable; 64] {
        // Since our message is <= one block in length, we can shortcut a step by
        // doubling the IV vector
        vec![2.0, 3.0, 5.0, 7.0, 11.0, 13.0, 17.0, 19.0]
            .into_iter()
            .flat_map(|p|
                Blake2s::word_to_le_nibbles(
                    f64::floor(2_f64.powi(32) * f64::fract(f64::sqrt(p))) as u32
                ).to_vec()
            )
            .map(|b|
                self.cs.add_input(BlsScalar::from(b as u64))
            )
            .collect::<Vec<Variable>>()
            .try_into()
            .unwrap()
    }

    fn compression(&mut self, h: &mut [Variable; 64], m: [Variable; 128], t: u8) {

        // Copied from RFC
        // 8*SIGMA[round][index]
        const SIGMA: [[usize; 16]; 10] = [         
            [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],
            [14,10,4,8,9,15,13,6,1,12,0,2,11,7,5,3],
            [11,8,12,0,5,2,15,13,10,14,3,6,7,1,9,4],
            [7,9,3,1,13,12,11,14,2,6,5,10,4,0,15,8],
            [9,0,5,7,2,4,10,15,14,1,11,12,6,8,3,13],
            [2,12,6,10,0,11,8,3,4,13,7,5,15,14,1,9],
            [12,5,1,15,14,13,4,10,0,7,6,3,9,2,8,11],
            [13,11,7,14,12,1,3,9,5,0,15,4,8,6,2,10],
            [6,15,14,9,11,3,0,8,12,2,13,7,1,4,10,5],
            [10,2,8,4,7,6,1,5,15,11,9,14,3,12,13,0],
        ];

        let iv = self.generate_iv();
        let mut v: [Variable; 128] = [*h, iv].concat().try_into().unwrap();

        // Our messages will never exceed one block, so the "final block"
        // flag is always true, and we always invert the bits of v[14].

        // Invert all bits in v[14] (represented here as v[112..120])
        // by XORing with [0xF, 0xF, 0xF, 0xF, 0xF, 0xF, 0xF, 0xF]
        let ff_var = self.cs.add_input(BlsScalar::from(0xf));
        let ff_vec = [ff_var; 8];

        self.xor(&mut v[112..120], &ff_vec);

        // XOR offset counter t=32 or t=64 is XORed into v[12], represented here as v[96]

        // in general, t is 16 nibbles long, but for our purposes only a single bit of
        // t is ever set, and we only need the nibble containing that bit, which is the
        // second nibble of t. Therefore only v[97] is XORed with 4 bits of t

        let t_hi_var = self.cs.add_input(BlsScalar::from((t >> 4) as u64));

        self.xor(&mut v[97..98], &[t_hi_var]);

        // Ten rounds of mixing for blake2s
        for i in 0..10
         {  
            self.mixing(&mut v, 0, 4,  8, 12, &m[8*SIGMA[i][ 0]..(8*SIGMA[i][ 0]+8)], &m[8*SIGMA[i][ 1]..(8*SIGMA[i][ 1]+8)]);
            self.mixing(&mut v, 1, 5,  9, 13, &m[8*SIGMA[i][ 2]..(8*SIGMA[i][ 2]+8)], &m[8*SIGMA[i][ 3]..(8*SIGMA[i][ 3]+8)]);
            self.mixing(&mut v, 2, 6, 10, 14, &m[8*SIGMA[i][ 4]..(8*SIGMA[i][ 4]+8)], &m[8*SIGMA[i][ 5]..(8*SIGMA[i][ 5]+8)]);
            self.mixing(&mut v, 3, 7, 11, 15, &m[8*SIGMA[i][ 6]..(8*SIGMA[i][ 6]+8)], &m[8*SIGMA[i][ 7]..(8*SIGMA[i][ 7]+8)]);

            self.mixing(&mut v, 0, 5, 10, 15, &m[8*SIGMA[i][ 8]..(8*SIGMA[i][ 8]+8)], &m[8*SIGMA[i][ 9]..(8*SIGMA[i][ 9]+8)]);
            self.mixing(&mut v, 1, 6, 11, 12, &m[8*SIGMA[i][10]..(8*SIGMA[i][10]+8)], &m[8*SIGMA[i][11]..(8*SIGMA[i][11]+8)]);
            self.mixing(&mut v, 2, 7,  8, 13, &m[8*SIGMA[i][12]..(8*SIGMA[i][12]+8)], &m[8*SIGMA[i][13]..(8*SIGMA[i][13]+8)]);
            self.mixing(&mut v, 3, 4,  9, 14, &m[8*SIGMA[i][14]..(8*SIGMA[i][14]+8)], &m[8*SIGMA[i][15]..(8*SIGMA[i][15]+8)]);
        }

        for i in 0..8 {
            self.xor_by_indices(&mut v, i, i+8);
            self.xor(&mut h[8*i..8*(i+1)], &v[8*i..8*(i+1)]);
        }
    }

    /// Blake2s with input and output both 256 bits, no personalization
    pub fn blake2s_256(&mut self, message: [Variable; 64]) -> [Variable; 64] {
        // initialize h
        let mut h = self.generate_iv();

        // XOR h[0] with parameter 0x01010000 ^ (kk << 8) ^ nn
        // key length kk = 0 bytes, input length nn = 32 bytes
        // 0x01010000 ^ (0x0 << 8) ^ 0x20 = 0x01010020 = [0x0, 0x2, 0x0, 0x0, 0x1, 0x0, 0x1, 0x0] in little endian
        let parameter_vec = vec![
            self.cs.zero_var(),
            self.cs.add_input(BlsScalar::from(2)),
            self.cs.zero_var(),
            self.cs.zero_var(),
            self.cs.add_input(BlsScalar::one()),
            self.cs.zero_var(),
            self.cs.add_input(BlsScalar::one()),
            self.cs.zero_var(),
            ];

        self.xor(&mut h[0..8], &parameter_vec);

        // pad the message to 64 bytes
        let m: [Variable; 128] = [message, [self.cs.zero_var(); 64]].concat().try_into().unwrap();

        // h := F( h, d[dd - 1], ll, TRUE )
        // ll = 32 bytes
        self.compression(&mut h, m, 32);

        h
    }

    /// Blake2s with input and output both 256 bits, with personalization
    pub fn blake2s_256_per(&mut self, message: [Variable; 64], personalization: [Variable; 16]) -> [Variable; 64] {
        // initialize h
        let mut h = self.generate_iv();

        // XOR h[0..8] with parameter 0x01010000 ^ (kk << 8) ^ nn
        // key length kk = 0 bytes, input length nn = 32 bytes
        // 0x01010000 ^ (0x0 << 8) ^ 0x20 = 0x01010020 = [0x0, 0x2, 0x0, 0x0, 0x1, 0x0, 0x1, 0x0] in little endian
        let param_word_1 = vec![
            self.cs.zero_var(),
            self.cs.add_input(BlsScalar::from(2)),
            self.cs.zero_var(),
            self.cs.zero_var(),
            self.cs.add_input(BlsScalar::one()),
            self.cs.zero_var(),
            self.cs.add_input(BlsScalar::one()),
            self.cs.zero_var(),
            ];

        self.xor(&mut h[0..8], &param_word_1);

        // XOR h[48..] with personalization
        self.xor(&mut h[48..], &personalization);

        // pad the message to 64 bytes
        let m: [Variable; 128] = [message, [self.cs.zero_var(); 64]].concat().try_into().unwrap();

        // h := F( h, d[dd - 1], ll, TRUE )
        // ll = 32 bytes
        self.compression(&mut h, m, 32);

        h
    }

    /// Blake2s with input 512 bits and output 256 bits
    pub fn blake2s_512(&mut self, message: [Variable; 128]) -> [Variable; 64] {
        // initialize h
        let mut h = self.generate_iv();

        // XOR h[0] with parameter 0x01010000 ^ (kk << 8) ^ nn
        // key length kk = 0 bytes, input length nn = 32 bytes
        // 0x01010000 ^ (0x0 << 8) ^ 0x20 = 0x01010020 = [0x20, 0x00, 0x01, 0x01] in little endian
        let parameter_vec = vec![self.cs.add_input(BlsScalar::from(32)), self.cs.zero_var(), self.cs.add_input(BlsScalar::one()), self.cs.add_input(BlsScalar::one())];

        self.xor(&mut h[0..8], &parameter_vec);
    
        // h := F( h, d[dd - 1], ll, TRUE )
        // ll = 64 bytes
        self.compression(&mut h, message, 64);

        h
    }

    fn scalar_to_nibble_vars(&mut self, scalar: BlsScalar) -> [Variable; 64] {
        scalar.reduce().0.iter()
            .flat_map(|v| vec![v % (1<<32), v >> 32])
            .flat_map(|u| Blake2s::word_to_le_nibbles(u as u32).to_vec())
            .map(|b| self.cs.add_input(BlsScalar::from(b as u64)))
            .collect::<Vec<Variable>>().try_into().unwrap()
    }

    /// Shows knowledge of a blake2s preimage of a hash
    pub fn blake2s_preimage(&mut self, preimage: BlsScalar, hash: BlsScalar) {
        let preimage_vars = self.scalar_to_nibble_vars(preimage);
        let circuit_result_vars = self.blake2s_256(preimage_vars);
        let circuit_result = self.compose_scalar_from_le_nibbles(&circuit_result_vars);
        let hash_var = self.cs.add_input(hash);
        self.cs.assert_equal(hash_var, circuit_result);        
    }

    fn vars_to_nibbles(&mut self, v: &[Variable]) -> Vec<u8> {
        v.iter().map(|b| (self.cs.variables[&b].reduce().0[0] % 16) as u8).collect::<Vec<u8>>()
    }

    fn print_words(&mut self, v: &[Variable]) {
        let nibbles = self.vars_to_nibbles(v);
        let mut words = vec![];
        for i in 0..16 {
            words.push(
                nibbles[8*i..8*(i+1)].iter().rev().fold(0u32, |acc, x| 16*acc + ((x % 16) as u32))
            )
        }
        std::println!("{:08x?}", words);
    }
}

#[cfg(test)]
mod tests {
    use dusk_bls12_381::BlsScalar;
    use crate::prelude::StandardComposer;
    use crate::constraint_system::{Variable, helper::*};
    use crate::proof_system::{Prover, Verifier};

    #[test]
    fn test_blake2s_preimage_prove_verify() {
        use crate::constraint_system::blake2s::blake2s_4bit::generate_blake_table;
        let lookup_table = generate_blake_table();

        let res = gadget_plookup_tester(
            |composer| {
                // generate blake2s 4-bit lookup table
                composer.append_lookup_table(&generate_blake_table());

                // prover's secret preimage
                let preimage = BlsScalar::zero();

                // blake2s hash of 256-bits of zeros
                let hash_bytes: [u8; 64] = [
                    0x32, 0x0b, 0x5e, 0xa9, 0x9e, 0x65, 0x3b, 0xc2, 0xb5, 0x93, 0xdb, 0x41, 0x30,
                    0xd1, 0x0a, 0x4e, 0xfd, 0x3a, 0x0b, 0x4c, 0xc2, 0xe1, 0xa6, 0x67, 0x2b, 0x67,
                    0x8d, 0x71, 0xdf, 0xbd, 0x33, 0xad, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                ];

                let hash = hash_bytes.iter().rev().fold(BlsScalar::zero(), |acc, x| BlsScalar::from(256)*acc + BlsScalar::from(*x as u64));

                composer.append_lookup_table(&generate_blake_table());

                composer.blake2s_preimage(preimage, hash);
                std::println!("gates: {:?}", composer.circuit_size());
            },
        9000,
        lookup_table,
        );
    }

    #[test]
    fn test_blake2s_hash() {
        use std::convert::TryInto;
        let mut composer = StandardComposer::new();

        // 256 bits of zeros
        let message_nibbles: [u8; 64] = [
            0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00,
        ];

        // blake2s hash of 256-bits of zeros
        let hash_nibbles: [u8; 64] = [
            0x2, 0x3, 0xb, 0x0, 0xe, 0x5, 0x9, 0xa, 
            0xe, 0x9, 0x5, 0x6, 0xb, 0x3, 0x2, 0xc,
            0x5, 0xb, 0x3, 0x9, 0xb, 0xd, 0x1, 0x4,
            0x0, 0x3, 0x1, 0xd, 0xa, 0x0, 0xe, 0x4,
            0xd, 0xf, 0xa, 0x3, 0xb, 0x0, 0xc, 0x4,
            0x2, 0xc, 0x1, 0xe, 0x6, 0xa, 0x7, 0x6,
            0xb, 0x2, 0x7, 0x6, 0xd, 0x8, 0x1, 0x7,
            0xf, 0xd, 0xd, 0xb, 0x3, 0x3, 0xd, 0xa
            ];

        let mut message_vars = [composer.zero_var(); 64];
        for i in 0..64 {
            message_vars[i] = composer.add_input(BlsScalar::from(message_nibbles[i] as u64));
        }
        let hash_vars = composer.blake2s_256(message_vars);

        std::println!("gates: {:?}", composer.circuit_size());
        for i in 0..64 {
            assert_eq!(composer.vars_to_nibbles(&hash_vars)[i], hash_nibbles[i]);
        }
    }
}