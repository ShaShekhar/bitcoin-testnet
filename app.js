function calc_mod(x, p){
	let mod;
	if(x < 0n){
		if((x+p) < 0n){
			mod = ((-1n*x/p)+1n)*p + x;
		} else {
			mod =  x + p;
		}
	} else{
		mod =  x % p;
	}
	return mod;
}
function extended_euclidean_algorithm(a, b){
	let old_r = a, r = b;
	let old_s = 1n, s = 0n;
	let old_t = 0n, t = 1n;
	let new_r, new_s, new_t, quotient;
	while (r !== 0n){
		if(old_r < 0n && r < 0n){
			quotient = old_r / r;
		} else if (old_r < 0n || r < 0n){
			quotient = (old_r / r) - 1n;
		} else {
			quotient = old_r / r;
		}
		new_r = old_r - quotient*r;
		old_r = r;
		r = new_r;
		new_s = old_s - quotient*s;
		old_s = s;
		s = new_s;
		new_t = old_t - quotient*t;
		old_t = t;
		t = new_t;
	}
	return [old_r, old_s, old_t];
}

function inverse(n, p){
	const [gcd, x, y] = extended_euclidean_algorithm(n, p);
	const mod_x = calc_mod(x, p);
	return mod_x;
}
class Point {
	constructor(x, y){
		this.curve_p = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2Fn;
		this.curve_a = 0x0000000000000000000000000000000000000000000000000000000000000000n;
		this.curve_b = 0x0000000000000000000000000000000000000000000000000000000000000007n;
		this.x = x;
		this.y = y;
	}
	add(other) {
		if (this == INF){
			return other;
		}
		if (other == INF){
			return this;
		}
		if (this.x == other.x && this.y != other.y){
			return INF;
		}
		let m;
		if (this.x == other.x){
			m = (3n * this.x**2n + this.curve_a) * inverse(2n * this.y, this.curve_p);
			m = calc_mod(m, this.curve_p);
		} else {
			m = (this.y - other.y) * inverse(this.x - other.x, this.curve_p);
			m = calc_mod(m, this.curve_p);
		}
		let rx, ry;
		rx = (m**2n - this.x - other.x);
		rx = calc_mod(rx, this.curve_p);
		ry = ((m*(this.x - rx)) - this.y);
		ry = calc_mod(ry, this.curve_p);
		return new Point(rx, ry);
	}
	multiply(k) {
		let result = INF;
		let append = this;
		while (k) {
			if (k & 1n){
				result = result.add(append);
			}
			append = append.add(append);
			k = k >> 1n;
		}
		return result;
	}
}
const Gx = 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798n;
const Gy = 0x483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8n;
const ORD_G = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141n;
INF = new Point(null, null);
const G = new Point(Gx, Gy);
function rotr(x, n, size=32) {
    return ((x >>> n) | (x << size-n) & (2**size-1)) >>> 0;
}
function shr(x, n) {
    return x >>> n;
}
function ch(x, y, z) {
    return ((x & y) ^ (~x & z)) >>> 0;
}
function maj(x, y, z) {
    return ((x & y) ^ (x & z) ^ (y & z)) >>> 0;
}
function sig0(x) {
    return (rotr(x, 7) ^ rotr(x, 18) ^ shr(x, 3)) >>> 0;
}
function sig1(x) {
    return (rotr(x, 17) ^ rotr(x, 19) ^ shr(x, 10)) >>> 0;
}
function capsig0(x) {
    return (rotr(x, 2) ^ rotr(x, 13) ^ rotr(x, 22)) >>> 0;
}
function capsig1(x) {
    return (rotr(x, 6) ^ rotr(x, 11) ^ rotr(x, 25)) >>> 0;
}
function first_n_primes(n){
    const primeArr = [];
    let num = 2;
    let isPrime = true;
    for(let i = 0; i < n; num++){
        for(let j = 2; j*j <= num; j++){
            if(num % j === 0){
                isPrime = false;
                break;
            }
        }
        if(!isPrime){
            isPrime = true;
        } else {
            primeArr.push(num);
            i++;
        }
    }
    return primeArr;
}
function frac_bin(f){
    let f1 = f - Math.floor(f);
    f1 = f1 * 0x100000000;
    f1 = parseInt(f1);
    return f1;
}
function genK(){
    const shaK = new Uint32Array(64);
    const primes64 = first_n_primes(64);
    primes64.forEach(function(prime, index){
        shaK[index] = frac_bin(Math.pow(prime, 1/3));
    });
    return shaK;
}
function genH(){
    const initialHash = new Uint32Array(8);
    const primes8 = first_n_primes(8);
    primes8.forEach(function(prime, index){
        initialHash[index] = frac_bin(Math.pow(prime, 1/2));
    });
    return initialHash;
}
function hexStringToArray_sha(hex_str){
    const out = [];
    const total_4b_chunk = parseInt(hex_str.length/8);
    const remaining_hex = hex_str.length % 8;
    for(let i = 0; i < total_4b_chunk; i++){
        out.push(parseInt(hex_str.substring(8*i, 8*i+8), 16));
    }
    if(remaining_hex){
        out.push(parseInt(hex_str.substring(8*total_4b_chunk), 16));
    }
    return out;
}
function pad_sha(hexString) {
    const msg_len = hexString.length*4;
    const last_w_len = (hexString.length % 8)*4;
    const data = hexStringToArray_sha(hexString);
    const uint32_data = new Uint32Array(data);
    let last_byte, remaining_bytes = [];
    if(last_w_len === 0) {
        remaining_bytes.push((1 << 31) >>> 0);

    }else if(last_w_len === 8 || last_w_len === 16 || last_w_len === 24){
        last_byte = uint32_data[uint32_data.length-1]
        last_byte = (last_byte << (32-last_w_len) | 1 << (32-last_w_len-1)) >>> 0;
        uint32_data.fill(last_byte, uint32_data.length-1);
    }
    while(true) {
        if((uint32_data.length*32 + remaining_bytes.length*32) % 512 === 448) {
            break;
        }
        remaining_bytes.push(0);    
    }
    if((uint32_data.length*32 + remaining_bytes.length*32) <= 2**32-1){
        remaining_bytes.push(0);
        remaining_bytes.push(msg_len);
    } else {
        throw new Error('Can only hash upto file size of 4GB.');
    }
    const uint32_padded_msg = new Uint32Array(uint32_data.length+remaining_bytes.length);
    uint32_data.forEach(function(num, index){
        uint32_padded_msg[index] = num;
    });
    remaining_bytes.forEach(function(num, index){
        uint32_padded_msg[index+uint32_data.length] = num;
    });
    return uint32_padded_msg;
}
function sha256(hex_data) {
    const K = genK();
    const padded_msg = pad_sha(hex_data);
    const msg_len = padded_msg.length*32;
    const BLOCK_SIZE = 512;
    let Hash = genH();
    let W, delta;
    let term1,term2,term3,term4,total,
    a,b,c,d,e,f,g,h,T1,T2;
    let padded_hex, hash_output='';
    for(let i = 0; i < msg_len/BLOCK_SIZE; i++){
        W = new Uint32Array(64);
        for(let j = 0; j < 64; j++){
            if(j <= 15){
                W[j] = padded_msg[16*i+j];
            } else {
                term1 = sig1(W[j-2]);
                term2 = W[j-7];
                term3 = sig0(W[j-15]);
                term4 = W[j-16];
                total = (term1 + term2 + term3 + term4) >>> 0;
                W[j] = total;
            }
        }
        [a, b, c, d, e, f, g, h] = Hash;
        for(let j = 0; j < 64; j++){
            T1 = (h + capsig1(e) + ch(e, f, g) + K[j] + W[j]) >>> 0;
            T2 = (capsig0(a) + maj(a, b, c)) >>> 0;
            h = g;
            g = f;
            f = e;
            e = (d + T1) >>> 0;
            d = c;
            c = b;
            b = a;
            a = (T1 + T2) >>> 0;
        }
        delta = [a, b, c, d, e, f, g, h];
        Hash.forEach(function(prev_hash, index){
            Hash[index] = (delta[index] + prev_hash) >>> 0;
        });
    }
    Hash.forEach(function(final_hash){
        padded_hex = (final_hash.toString(16)).padStart(8, '0');
        hash_output += padded_hex;
    });
    return hash_output;
}
let K0 = 0x00000000,
    K1 = 0x5A827999,
    K2 = 0x6ED9EBA1,
    K3 = 0x8F1BBCDC,
    K4 = 0xA953FD4E;
let KK0 = 0x50A28BE6,
    KK1 = 0x5C4DD124,
    KK2 = 0x6D703EF3,
    KK3 = 0x7A6D76E9,
    KK4 = 0x00000000;
function ROL(x, n){
    return (((x << n) & 0xffffffff) | ((x >>> (32-n)))) >>> 0;
}
function F0(x, y, z){
    return (x ^ y ^ z) >>> 0;
}
function F1(x, y, z){
    return ((x & y) |(((~x) % 0x100000000) & z)) >>> 0;
}
function F2(x, y, z){
    return ((x | ((~y) % 0x100000000)) ^ z) >>> 0;
}
function F3(x, y, z){
    return (x & z) | (y & ((~z) % 0x100000000)) >>> 0;
}
function F4(x, y, z){
    return (x ^ (y | ((~z) % 0x100000000))) >>> 0;
}
function R(a, b, c, d, e, Fj, Kj, sj, rj, X){
    a = ((ROL((a + Fj(b, c, d) + X[rj] + Kj) % 0x100000000, sj) + e) % 0x100000000) >>> 0;
    c = ROL(c, 10);
    return [a, c];
}
function changeEndianness(string){
    const result = [];
    let len = parseInt(string.length/2);
    for(let i = 0; i < len; i++){
        result.unshift(string.substring(2*i, 2*i+2));
    }
    return result.join('');
}
function hexStringToArray_ripemd(hex_str){
    const out = [];
    const hex_length = parseInt(hex_str.length/8);
    const remaining_hex = hex_str.length % 8;
    let little_end;
    for(let i = 0; i < hex_length; i++){
        little_end = changeEndianness(hex_str.substring(8*i, 8*i+8))
        out.push(parseInt(little_end, 16));
    }
    if(remaining_hex){
        little_end = hex_str.substring(8*hex_length);
        out.push(parseInt(little_end, 16));
    }
    return out;
}

function pad_ripemd(hexString) {
    const msg_len = hexString.length*4;
    const last_w_len = (hexString.length % 8)*4;
    data = hexStringToArray_ripemd(hexString);
    const uint32_data = new Uint32Array(data);
    let last_byte, remaining_bytes = [];
    if(last_w_len === 0) {
        remaining_bytes.push((1 << 7) >>> 0);

    }else if(last_w_len === 8 || last_w_len === 16 || last_w_len === 24){
        last_byte = uint32_data[uint32_data.length-1]
        last_byte = (last_byte | 1 << (last_w_len+7)) >>> 0;
        uint32_data.fill(last_byte, uint32_data.length-1);
    }
    while(true) {
        if((uint32_data.length*32 + remaining_bytes.length*32) % 512 === 448) {
            break;
        }
        remaining_bytes.push(0);    
    }
    if((uint32_data.length*32 + remaining_bytes.length*32) <= 2**32-1){
        remaining_bytes.push(msg_len);
        remaining_bytes.push(0);
    } else {
        throw new Error('Can only hash upto file size of 4GB.');
    }
    const uint32_padded_msg = new Uint32Array(uint32_data.length+remaining_bytes.length);
    uint32_data.forEach(function(num, index){
        uint32_padded_msg[index] = num;
    });
    remaining_bytes.forEach(function(num, index){
        uint32_padded_msg[index+uint32_data.length] = num;
    });
    return uint32_padded_msg;
}
function RIPEMD160Transform(state, M){
    let a, b, c, d, e;
    let aa, bb, cc, dd, ee;
    a = state[0];
    b = state[1];
    c = state[2];
    d = state[3];
    e = state[4];
    [a, c] = R(a, b, c, d, e, F0, K0, 11,  0, M);
    [e, b] = R(e, a, b, c, d, F0, K0, 14,  1, M);
    [d, a] = R(d, e, a, b, c, F0, K0, 15,  2, M);
    [c, e] = R(c, d, e, a, b, F0, K0, 12,  3, M);
    [b, d] = R(b, c, d, e, a, F0, K0,  5,  4, M);
    [a, c] = R(a, b, c, d, e, F0, K0,  8,  5, M);
    [e, b] = R(e, a, b, c, d, F0, K0,  7,  6, M);
    [d, a] = R(d, e, a, b, c, F0, K0,  9,  7, M);
    [c, e] = R(c, d, e, a, b, F0, K0, 11,  8, M);
    [b, d] = R(b, c, d, e, a, F0, K0, 13,  9, M);
    [a, c] = R(a, b, c, d, e, F0, K0, 14, 10, M);
    [e, b] = R(e, a, b, c, d, F0, K0, 15, 11, M);
    [d, a] = R(d, e, a, b, c, F0, K0,  6, 12, M);
    [c, e] = R(c, d, e, a, b, F0, K0,  7, 13, M);
    [b, d] = R(b, c, d, e, a, F0, K0,  9, 14, M);
    [a, c] = R(a, b, c, d, e, F0, K0,  8, 15, M);
    [e, b] = R(e, a, b, c, d, F1, K1,  7,  7, M);
    [d, a] = R(d, e, a, b, c, F1, K1,  6,  4, M);
    [c, e] = R(c, d, e, a, b, F1, K1,  8, 13, M);
    [b, d] = R(b, c, d, e, a, F1, K1, 13,  1, M);
    [a, c] = R(a, b, c, d, e, F1, K1, 11, 10, M);
    [e, b] = R(e, a, b, c, d, F1, K1,  9,  6, M);
    [d, a] = R(d, e, a, b, c, F1, K1,  7, 15, M);
    [c, e] = R(c, d, e, a, b, F1, K1, 15,  3, M);
    [b, d] = R(b, c, d, e, a, F1, K1,  7, 12, M);
    [a, c] = R(a, b, c, d, e, F1, K1, 12,  0, M);
    [e, b] = R(e, a, b, c, d, F1, K1, 15,  9, M);
    [d, a] = R(d, e, a, b, c, F1, K1,  9,  5, M);
    [c, e] = R(c, d, e, a, b, F1, K1, 11,  2, M);
    [b, d] = R(b, c, d, e, a, F1, K1,  7, 14, M);
    [a, c] = R(a, b, c, d, e, F1, K1, 13, 11, M);
    [e, b] = R(e, a, b, c, d, F1, K1, 12,  8, M);
    [d, a] = R(d, e, a, b, c, F2, K2, 11,  3, M);
    [c, e] = R(c, d, e, a, b, F2, K2, 13, 10, M);
    [b, d] = R(b, c, d, e, a, F2, K2,  6, 14, M);
    [a, c] = R(a, b, c, d, e, F2, K2,  7,  4, M);
    [e, b] = R(e, a, b, c, d, F2, K2, 14,  9, M);
    [d, a] = R(d, e, a, b, c, F2, K2,  9, 15, M);
    [c, e] = R(c, d, e, a, b, F2, K2, 13,  8, M);
    [b, d] = R(b, c, d, e, a, F2, K2, 15,  1, M);
    [a, c] = R(a, b, c, d, e, F2, K2, 14,  2, M);
    [e, b] = R(e, a, b, c, d, F2, K2,  8,  7, M);
    [d, a] = R(d, e, a, b, c, F2, K2, 13,  0, M);
    [c, e] = R(c, d, e, a, b, F2, K2,  6,  6, M);
    [b, d] = R(b, c, d, e, a, F2, K2,  5, 13, M);
    [a, c] = R(a, b, c, d, e, F2, K2, 12, 11, M);
    [e, b] = R(e, a, b, c, d, F2, K2,  7,  5, M);
    [d, a] = R(d, e, a, b, c, F2, K2,  5, 12, M);
    [c, e] = R(c, d, e, a, b, F3, K3, 11,  1, M);
    [b, d] = R(b, c, d, e, a, F3, K3, 12,  9, M);
    [a, c] = R(a, b, c, d, e, F3, K3, 14, 11, M);
    [e, b] = R(e, a, b, c, d, F3, K3, 15, 10, M);
    [d, a] = R(d, e, a, b, c, F3, K3, 14,  0, M);
    [c, e] = R(c, d, e, a, b, F3, K3, 15,  8, M);
    [b, d] = R(b, c, d, e, a, F3, K3,  9, 12, M);
    [a, c] = R(a, b, c, d, e, F3, K3,  8,  4, M);
    [e, b] = R(e, a, b, c, d, F3, K3,  9, 13, M);
    [d, a] = R(d, e, a, b, c, F3, K3, 14,  3, M);
    [c, e] = R(c, d, e, a, b, F3, K3,  5,  7, M);
    [b, d] = R(b, c, d, e, a, F3, K3,  6, 15, M);
    [a, c] = R(a, b, c, d, e, F3, K3,  8, 14, M);
    [e, b] = R(e, a, b, c, d, F3, K3,  6,  5, M);
    [d, a] = R(d, e, a, b, c, F3, K3,  5,  6, M);
    [c, e] = R(c, d, e, a, b, F3, K3, 12,  2, M);
    [b, d] = R(b, c, d, e, a, F4, K4,  9,  4, M);
    [a, c] = R(a, b, c, d, e, F4, K4, 15,  0, M);
    [e, b] = R(e, a, b, c, d, F4, K4,  5,  5, M);
    [d, a] = R(d, e, a, b, c, F4, K4, 11,  9, M);
    [c, e] = R(c, d, e, a, b, F4, K4,  6,  7, M);
    [b, d] = R(b, c, d, e, a, F4, K4,  8, 12, M);
    [a, c] = R(a, b, c, d, e, F4, K4, 13,  2, M);
    [e, b] = R(e, a, b, c, d, F4, K4, 12, 10, M);
    [d, a] = R(d, e, a, b, c, F4, K4,  5, 14, M);
    [c, e] = R(c, d, e, a, b, F4, K4, 12,  1, M);
    [b, d] = R(b, c, d, e, a, F4, K4, 13,  3, M);
    [a, c] = R(a, b, c, d, e, F4, K4, 14,  8, M);
    [e, b] = R(e, a, b, c, d, F4, K4, 11, 11, M);
    [d, a] = R(d, e, a, b, c, F4, K4,  8,  6, M);
    [c, e] = R(c, d, e, a, b, F4, K4,  5, 15, M);
    [b, d] = R(b, c, d, e, a, F4, K4,  6, 13, M);
    aa = a;
    bb = b;
    cc = c;
    dd = d;
    ee = e;
    a = state[0];
    b = state[1];
    c = state[2];
    d = state[3];
    e = state[4];
    [a, c] = R(a, b, c, d, e, F4, KK0,  8,  5, M);
    [e, b] = R(e, a, b, c, d, F4, KK0,  9, 14, M);
    [d, a] = R(d, e, a, b, c, F4, KK0,  9,  7, M);
    [c, e] = R(c, d, e, a, b, F4, KK0, 11,  0, M);
    [b, d] = R(b, c, d, e, a, F4, KK0, 13,  9, M);
    [a, c] = R(a, b, c, d, e, F4, KK0, 15,  2, M);
    [e, b] = R(e, a, b, c, d, F4, KK0, 15, 11, M);
    [d, a] = R(d, e, a, b, c, F4, KK0,  5,  4, M);
    [c, e] = R(c, d, e, a, b, F4, KK0,  7, 13, M);
    [b, d] = R(b, c, d, e, a, F4, KK0,  7,  6, M);
    [a, c] = R(a, b, c, d, e, F4, KK0,  8, 15, M);
    [e, b] = R(e, a, b, c, d, F4, KK0, 11,  8, M);
    [d, a] = R(d, e, a, b, c, F4, KK0, 14,  1, M);
    [c, e] = R(c, d, e, a, b, F4, KK0, 14, 10, M);
    [b, d] = R(b, c, d, e, a, F4, KK0, 12,  3, M);
    [a, c] = R(a, b, c, d, e, F4, KK0,  6, 12, M);
    [e, b] = R(e, a, b, c, d, F3, KK1,  9,  6, M);
    [d, a] = R(d, e, a, b, c, F3, KK1, 13, 11, M);
    [c, e] = R(c, d, e, a, b, F3, KK1, 15,  3, M);
    [b, d] = R(b, c, d, e, a, F3, KK1,  7,  7, M);
    [a, c] = R(a, b, c, d, e, F3, KK1, 12,  0, M);
    [e, b] = R(e, a, b, c, d, F3, KK1,  8, 13, M);
    [d, a] = R(d, e, a, b, c, F3, KK1,  9,  5, M);
    [c, e] = R(c, d, e, a, b, F3, KK1, 11, 10, M);
    [b, d] = R(b, c, d, e, a, F3, KK1,  7, 14, M);
    [a, c] = R(a, b, c, d, e, F3, KK1,  7, 15, M);
    [e, b] = R(e, a, b, c, d, F3, KK1, 12,  8, M);
    [d, a] = R(d, e, a, b, c, F3, KK1,  7, 12, M);
    [c, e] = R(c, d, e, a, b, F3, KK1,  6,  4, M);
    [b, d] = R(b, c, d, e, a, F3, KK1, 15,  9, M);
    [a, c] = R(a, b, c, d, e, F3, KK1, 13,  1, M);
    [e, b] = R(e, a, b, c, d, F3, KK1, 11,  2, M);
    [d, a] = R(d, e, a, b, c, F2, KK2,  9, 15, M);
    [c, e] = R(c, d, e, a, b, F2, KK2,  7,  5, M);
    [b, d] = R(b, c, d, e, a, F2, KK2, 15,  1, M);
    [a, c] = R(a, b, c, d, e, F2, KK2, 11,  3, M);
    [e, b] = R(e, a, b, c, d, F2, KK2,  8,  7, M);
    [d, a] = R(d, e, a, b, c, F2, KK2,  6, 14, M);
    [c, e] = R(c, d, e, a, b, F2, KK2,  6,  6, M);
    [b, d] = R(b, c, d, e, a, F2, KK2, 14,  9, M);
    [a, c] = R(a, b, c, d, e, F2, KK2, 12, 11, M);
    [e, b] = R(e, a, b, c, d, F2, KK2, 13,  8, M);
    [d, a] = R(d, e, a, b, c, F2, KK2,  5, 12, M);
    [c, e] = R(c, d, e, a, b, F2, KK2, 14,  2, M);
    [b, d] = R(b, c, d, e, a, F2, KK2, 13, 10, M);
    [a, c] = R(a, b, c, d, e, F2, KK2, 13,  0, M);
    [e, b] = R(e, a, b, c, d, F2, KK2,  7,  4, M);
    [d, a] = R(d, e, a, b, c, F2, KK2,  5, 13, M);
    [c, e] = R(c, d, e, a, b, F1, KK3, 15,  8, M);
    [b, d] = R(b, c, d, e, a, F1, KK3,  5,  6, M);
    [a, c] = R(a, b, c, d, e, F1, KK3,  8,  4, M);
    [e, b] = R(e, a, b, c, d, F1, KK3, 11,  1, M);
    [d, a] = R(d, e, a, b, c, F1, KK3, 14,  3, M);
    [c, e] = R(c, d, e, a, b, F1, KK3, 14, 11, M);
    [b, d] = R(b, c, d, e, a, F1, KK3,  6, 15, M);
    [a, c] = R(a, b, c, d, e, F1, KK3, 14,  0, M);
    [e, b] = R(e, a, b, c, d, F1, KK3,  6,  5, M);
    [d, a] = R(d, e, a, b, c, F1, KK3,  9, 12, M);
    [c, e] = R(c, d, e, a, b, F1, KK3, 12,  2, M);
    [b, d] = R(b, c, d, e, a, F1, KK3,  9, 13, M);
    [a, c] = R(a, b, c, d, e, F1, KK3, 12,  9, M);
    [e, b] = R(e, a, b, c, d, F1, KK3,  5,  7, M);
    [d, a] = R(d, e, a, b, c, F1, KK3, 15, 10, M);
    [c, e] = R(c, d, e, a, b, F1, KK3,  8, 14, M);
    [b, d] = R(b, c, d, e, a, F0, KK4,  8, 12, M);
    [a, c] = R(a, b, c, d, e, F0, KK4,  5, 15, M);
    [e, b] = R(e, a, b, c, d, F0, KK4, 12, 10, M);
    [d, a] = R(d, e, a, b, c, F0, KK4,  9,  4, M);
    [c, e] = R(c, d, e, a, b, F0, KK4, 12,  1, M);
    [b, d] = R(b, c, d, e, a, F0, KK4,  5,  5, M);
    [a, c] = R(a, b, c, d, e, F0, KK4, 14,  8, M);
    [e, b] = R(e, a, b, c, d, F0, KK4,  6,  7, M);
    [d, a] = R(d, e, a, b, c, F0, KK4,  8,  6, M);
    [c, e] = R(c, d, e, a, b, F0, KK4, 13,  2, M);
    [b, d] = R(b, c, d, e, a, F0, KK4,  6, 13, M);
    [a, c] = R(a, b, c, d, e, F0, KK4,  5, 14, M);
    [e, b] = R(e, a, b, c, d, F0, KK4, 15,  0, M);
    [d, a] = R(d, e, a, b, c, F0, KK4, 13,  3, M);
    [c, e] = R(c, d, e, a, b, F0, KK4, 11,  9, M);
    [b, d] = R(b, c, d, e, a, F0, KK4, 11, 11, M);
    t = (state[1] + cc + d) % 0x100000000;
    state[1] = (state[2] + dd + e) % 0x100000000;
    state[2] = (state[3] + ee + a) % 0x100000000;
    state[3] = (state[4] + aa + b) % 0x100000000;
    state[4] = (state[0] + bb + c) % 0x100000000;
    state[0] = t;
    return state;
}
function RIPEMD160(data){
    let state = new Uint32Array([0x67452301, 0xEFCDAB89, 0x98BADCFE, 0x10325476, 0xC3D2E1F0]);
    const padded_msg = pad_ripemd(data);
    const msg_len = padded_msg.length*32;
    const BLOCK_SIZE = 512;
    let hash_output = '';
    let W, padded_hex;
    for(let i = 0; i < msg_len/BLOCK_SIZE; i++){
        W = new Uint32Array(16);
        for(let j = 0; j < 16; j++){
            W[j] = padded_msg[16*i+j];
        }
        state = RIPEMD160Transform(state, W);
    }
    state.forEach(function(final_hash){
        padded_hex = (final_hash.toString(16)).padStart(8, '0');
        hash_output += changeEndianness(padded_hex);
    });
    return hash_output
}
function gen_bigRandom_int(){
    const random_num = new Uint8Array(32);
    const rand_array = window.crypto.getRandomValues(random_num);
    let temp_str, bigInt_bin = '0b';
    rand_array.forEach(function(num){
         temp_str = num.toString(2).padStart(8, '0');
         bigInt_bin += temp_str;
    });
    const bigInt = BigInt(bigInt_bin);
    return bigInt;
}
function gen_secret_key(){
    let private_key;
    while(true){
        private_key = gen_bigRandom_int();
        if(private_key < ORD_G){
            break;
        }
    }
    return private_key;
}
class PublicKey extends Point {
    static from_sk(sk){
        if(typeof sk !== 'bigint'){
            throw new Error('sk must be BigInt type');
        }
        const from_point = G.multiply(sk);
        return new PublicKey(from_point.x, from_point.y);
    }
    decode(pk_hex){
        if(typeof pk_hex !== 'string'){
            throw new Error('Public Key must be hex string');
        }
        if(pk_hex.substring(0, 2) === '04'){
            const x = BigInt('0x' + pk_hex.substring(2, 66));
            const y = BigInt('0x' + pk_hex.substring(66, 130));
            return new PublicKey(x, y);
        }
        const is_even = pk_hex.substring(0, 2) === '02';
        const x = BigInt('0x' + pk_hex.substring(2));
        const y2 = (((x*x) % this.p)*x + 7n) % this.p;
        let y = y2;
        for(let i = 1n; i < (this.p+1n)/4n; i++){
            y = (y*y2) % this.p;
        }
        if((y % 2n === 0n) === is_even){
            y = y;
        } else {
            y = this.p - y;
        }
        return new PublicKey(x, y);
    }
    encode(compressed, h160=true){
        let prefix, pk_bin, temp_x, temp_y;
        if(compressed){
            if(this.y % 2n === 0n){
                prefix = '02';
            } else {
                prefix = '03';
            }
            pk_bin = prefix + (this.x.toString(16)).padStart(64, '0');
        } else {
            prefix = '04';
            temp_x = (this.x.toString(16)).padStart(64, '0');
            temp_y = (this.y.toString(16)).padStart(64, '0');
            pk_bin = prefix + temp_x + temp_y;
        }
        if(h160){
            const sha_output = sha256(pk_bin);
            const ripemd160_output = RIPEMD160(sha_output);
            return ripemd160_output;
        }
        return pk_bin;
    }
    bitcoin_address(net, compressed, h160){
        const pkb_hash = this.encode(compressed, h160);
        let version;
        if(net === 'main'){
            version = '00';
        } else if(net === 'test'){
            version = '6f';
        }
        const ver_pkb_hash = version + pkb_hash;
        const checksum = sha256(sha256(ver_pkb_hash));
        const byte_address = ver_pkb_hash + checksum.substring(0, 8);
        const b58check_address = b58encode(byte_address);
        return b58check_address;
    }
}
function calc_HD_key(var_seed, fixed_priv_key){
    const hex_key = var_seed.toString(16).padStart(8, '0');
    const hex_message = fixed_priv_key.toString(16).padStart(64, '0');
    const innerContent = hex_key + hex_message;
    const innerHash = sha256(innerContent);
    const outerContent = hex_key + innerHash;
    const outerHash = sha256(outerContent);
    return outerHash;
}
const ALPHABET = '123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz';
const btc_addr_1 = document.getElementById('addr-1');
let CLICK_COUNTER = 0;
let MASTER_PRIVATE_KEY, MASTER_SEED = 0;
btc_addr_1.addEventListener('click', function(){
    CLICK_COUNTER += 1;
    if(CLICK_COUNTER === 1){
        MASTER_PRIVATE_KEY = gen_secret_key();
        document.getElementById('master_privkey').value = `${MASTER_PRIVATE_KEY}`;
    }
    let HD_PRIVATE_KEY;
    while(true){
        HD_PRIVATE_KEY = calc_HD_key(MASTER_SEED, MASTER_PRIVATE_KEY);
        HD_PRIVATE_KEY = BigInt('0x'+HD_PRIVATE_KEY);
        if(HD_PRIVATE_KEY < ORD_G){
            break;
        } else{
            MASTER_SEED += 1;
        }
    }
    if(CLICK_COUNTER === 1){
        document.getElementById('master_seed').value = MASTER_SEED;
    }
    const PubKey_Obj = PublicKey.from_sk(HD_PRIVATE_KEY);
    const btc_addr = PubKey_Obj.bitcoin_address('test', true, true);
    document.getElementById('saved_addr1').value = btc_addr;
    document.getElementById('seed1').value = MASTER_SEED;
    btc_addr_1.nextElementSibling.value = btc_addr;
    const a_tag = document.createElement('a');
    a_tag.id = 'temp-id1';
    a_tag.setAttribute('href', `https://www.blockchain.com/btc-testnet/address/${btc_addr}`);
    a_tag.setAttribute('target', '_blank');
    a_tag.appendChild(document.createTextNode('Verify that this address has never transacted before'));
    const link = document.getElementById('link-1');
    if(link.children.length === 0){
        link.appendChild(a_tag);
    } else {
        const old_heading = document.getElementById('temp-id1');
        link.replaceChild(a_tag, old_heading);
    }
    MASTER_SEED += 1;
});
document.getElementById('cal_address_btn').disabled = true;
document.getElementById('privKey_enter').addEventListener('click', (e) => {
    e.target.disabled = true;
    e.target.classList.remove('btn-outline-dark');
    e.target.classList.add('btn-outline-secondary');
    const cal_address = document.getElementById('cal_address_btn');
    cal_address.classList.remove('btn-outline-secondary');
    cal_address.classList.add('btn-outline-primary');
    cal_address.disabled = false;
    document.getElementById('master_privkey').readOnly = false;
    const seed = document.getElementById('master_seed');
    seed.readOnly = false;
    seed.value = 0;
});
document.getElementById('cal_address_btn').addEventListener('click', (e) => {
    if(!document.getElementById('master_privkey').readOnly){
        e.target.disabled = true;
        const master_key = BigInt(document.getElementById('master_privkey').value);
        const seed = parseInt(document.getElementById('master_seed').value);
        let calHDKEY;
        if(seed === 0){
            calHDKEY = master_key;
        } else {
            calHDKEY = calc_HD_key(seed, master_key);
            calHDKEY = BigInt('0x'+calHDKEY);
        }
        const btc_addr = PublicKey.from_sk(calHDKEY).bitcoin_address('test', true, true);
        document.getElementById('cal_address').value = btc_addr;
    }
});
function b58encode(byte_address){
    let n = BigInt('0x' + byte_address);
    const chars = [];
    let i;
    while(n){
        i = n % 58n;
        n = n / 58n;
        chars.push(ALPHABET[i]);
    }
    let num_zeros = 0;
    while(true){
        if(byte_address.substring(2*num_zeros,2*num_zeros+2) === '00'){
            num_zeros += 1;
        } else {
            break;
        }
    }
    if(num_zeros === 0){
        return chars.reverse().join('');
    } else {
        const res = num_zeros * ALPHABET[0] + chars.reverse().join('');
        return res;
    }
}
class Signature {
    constructor(r, s){
        this.r = r;
        this.s = s;
    }
    decode(der_hex){
       if(der_hex.substring(0, 2) !== '30'){
           throw new Error('der initial marker is not correct');
       } 
       let length = der_hex.substring(2, 4);
       length = parseInt(length, 16);
       if(length !== der_hex.length-2){
           throw new Error('der length is not correct');
       }
       if(der_hex.substring(4, 6) !== '02'){
           throw new Error('der r marker is not correct');
        }
       let rlength = der_hex.substring(6, 8);
       rlength = parseInt(rlength, 16);
       let rval = der_hex.substring(8, 8+rlength);
       rval = BigInt('0x' + rval);
       if(der_hex.substring(8+rlength, 8+rlength+2) !== '02'){
           throw new Error('der s marker is not correct');
        }
        let slength = der_hex.substring(8+rlength+2, 8+rlength+2+2);
        slength = parseInt(slength, 16);
        let sval = der_hex.substring(8+rlength+2+2, 8+rlength+2+2+slength);
        rval = BigInt('0x' + sval);
        if(der_hex.length !== 6+rlength+slength){
            throw new Error('der signature Length mismatch');
        }
        return Signature(rval, sval);
    }
    encode(){
        function der_sig(n){
            let nb = (n.toString(16)).padStart(64, '0');
            let counter = 0;
            while(true){
                if(nb.substring(2*counter, 2*counter+2) === '00'){
                    counter += 1;
                } else {
                    break;
                }
            }
            nb = nb.substring(counter);
            if(parseInt(nb.substring(0, 2), 16) >= 0x80){
                nb = '00' + nb;
            } 
            return nb;
        }
        const rb = der_sig(this.r);
        const sb = der_sig(this.s);
        const rb_content = '02' + parseInt(rb.length/2).toString(16).padStart(2, '0') + rb;
        const sb_content = '02' + parseInt(sb.length/2).toString(16).padStart(2, '0') + sb;
        const content_len = parseInt((rb_content.length+sb_content.length)/2);
        let frame = '30' + content_len.toString(16).padStart(2, '0');
        frame = frame + rb_content + sb_content;
        return frame;
    }
}
function sign(secret_key, message){
    let z = sha256(sha256(message));
    z = BigInt('0x' + z);
    const sk = gen_secret_key();
    const pk = PublicKey.from_sk(sk);
    const r = pk.x;
    let s = ((z + secret_key*r) * inverse(sk, ORD_G)) % ORD_G;
    if(s > ORD_G/2n){
        s = ORD_G - s;
    }
    return new Signature(r, s);
}
function verify(PUB_KEY, message, sig){
    if(typeof sig.r !== 'bigint' && sig.r > ORD_G && sig.r < 1){
        throw new Error('signature, r incorrect.');
    }
    if(typeof sig.s !== 'bigint' && sig.s > ORD_G && sig.s < 1){
        throw new Error('signature, s incorrect.');
    }
    let z = sha256(sha256(message));
    z = BigInt('0x' + z);
    w = inverse(sig[1], ORD_G);
    const u1 = (z * w) % ORD_G;
    const u2 = (sig[0] * w) % ORD_G;
    const P = (G.multiply(u1)).add(PUB_KEY.multiply(u2));
    const match = P.x === sig.r;
    return match;
}
function little_endian_to_int(hex_str, nbytes){
    if(nbytes > 1){
        const result = [];
        for(let i = 0; i < hex_str.length/2; i++){
            result.unshift(hex_str.substring(2*i, 2*i+2));
        }
        return parseInt(result.join(''), 16);
    }
    return parseInt(hex_str, 16);
}
function int_to_little_endian(int, nbytes){
    const data_hex = (int.toString(16)).padStart(nbytes*2, '0');
    if(nbytes > 1){
        const result = [];
        for(let i = 0; i < data_hex.length/2; i++){
            result.unshift(data_hex.substring(2*i, 2*i+2));
        }
        return result.join('');
    }
    return data_hex;
}
function big_to_little_endian(hex){
    const result = [];
    for(let i = 0; i < hex.length/2; i++){
        result.unshift(hex.substring(2*i, 2*i+2));
    }
    return result.join('');
}
function little_to_big_endian(hex){
    const result = [];
    for(let i = 0; i < hex.length/2; i++){
        result.unshift(hex.substring(2*i, 2*i+2));
    }
    return result.join('');
}
function encode_varint(i){
    if(i < 0xfd){
        return int_to_little_endian(i, 1);
    } else if(i < 0x10000){
        return 'fd' + int_to_little_endian(i, 2);
    } else if(i < 0x100000000){
        return 'fe' + int_to_little_endian(i, 4);
    } else if(i < 0x10000000000000000){
        return 'ff' + int_to_little_endian(i, 8);
    } else {
        throw new Error(`integer too large: ${i}`);
    }
}
function decode_varint(s){
    const i = little_endian_to_int(s.substring(0, 2), 1);
    if(i === 0xfd){
        return [little_endian_to_int(s.substring(2, 6), 2), s.substring(6)];
    } else if(i === 0xfe){
        return [little_endian_to_int(s.substring(2, 10), 4), s.substring(10)];
    } else if(i === 0xff){
        return [little_endian_to_int(s.substring(2, 18), 8), s.substring(18)];
    } else {
        return [i, s.substring(2)];
    }
}
class TxIn {
    constructor(prev_tx_id, tx_index, script_sig, sequence=0xffffffff){
        this.prev_tx_id = prev_tx_id;
        this.tx_index = tx_index;
        this.script_sig = script_sig;
        this.sequence = sequence;
        this.witness = null;
        this.net = 'test';
    }
    static decode(s, segwit_flag){
        const prev_tx_id = little_to_big_endian(s.substring(0, 64));
        const tx_index = little_endian_to_int(s.substring(64, 72), 4);
        let [length, str] = decode_varint(s.substring(36));
        const script_sig = Script.decode(str.substring(0, length));
        const sequence = little_endian_to_int(str.substring(length, length+8), 4);
        return {
            TxIn_Obj: new TxIn(prev_tx_id, tx_index, script_sig),
            remaining_str: str.substring(length+8),
        }
    }
    encode(script_override){
        const out = [];
        out.push(big_to_little_endian(this.prev_tx_id));
        out.push(int_to_little_endian(this.tx_index, 4));
        if(script_override === null){
            out.push(this.script_sig.encode());
        } else if(script_override === true){
            out.push(this.script_sig.encode());
        } else if(script_override === false){
            out.push(new Script([]).encode());
        } else {
            throw new Error("script_override must be one of null|true|false");
        }
        out.push(int_to_little_endian(this.sequence, 4));
        return out.join('');
    }
    get_value(){
        const tx = TxFetcher.fetch(this.prev_tx_id, net=this.net);
        const amount = tx.tx_outs[this.prev_tx_id].amount;
        return amount;
    }
    script_pubkey(){
        const tx = TxFetcher.fetch(this.prev_tx_id, net=this.net);
        const script = tx.tx_outs[this.tx_index].script_pubkey;
        return script;
    }
}
class TxOut {
    constructor(amount, script_pubkey){
        this.amount = amount;
        this.script_pubkey = script_pubkey;
    }
    static decode(s){
        const amount = little_endian_to_int(s.substring(0, 16), 8);
        const script_pubkey = Script.decode(s.substring(8));

        return {
            TxOut_Obj: new TxOut(amount, script_pubkey.script_obj),
            remaining_str: script_pubkey.remaining_str,
        }
    }
    encode(){
        const out = [];
        out.push(int_to_little_endian(this.amount, 8));
        out.push(this.script_pubkey.encode());
        return out.join('');
    }
}
class Tx {
    constructor(version, tx_ins, tx_outs, locktime, segwit){
        this.version = version; 
        this.tx_ins = tx_ins;
        this.tx_outs = tx_outs;
        this.locktime = locktime;
        this.segwit = segwit;
    }
    static decode(hex_str){
        const version = little_endian_to_int(hex_str.substring(0, 8), 4);
        let num_inputs, s, segwit = false;
        if(hex_str.substring(8, 10) === '00'){
            if(hex_str.substring(10, 12) === '01'){
                [num_inputs, s] = decode_varint(hex_str.substring(12));
                segwit = true;
                console.log(`s: ${s}`);
            }
        } else {
            [num_inputs, s] = decode_varint(hex_str.substring(8));
        }

        const inputs = [];
        let TxIns;
        for(let i = 0; i < num_inputs; i++){
            TxIns = TxIn.decode(s, this.segwit);
            inputs.push(TxIns.TxIn_Obj);
            s = TxIns.remaining_str;
        }
        [num_outputs, s] = decode_varint(s);
        const outputs = [];
        let TxOuts;
        for(let i = 0; i < num_outputs; i++){
            TxOuts = TxOut.decode(s);
            outputs.push(TxOuts.TxOut_Obj);
            s = TxOuts.remaining_str;
        }
        if(segwit){
            let num_items, items, item_len;
            for(let i = 0; i < inputs.length; i++){
                [num_items, s] = decode_varint(s);
                items = [];
                for(let i = 0; i < num_items; i++){
                    [item_len, s] = decode_varint(s);
                    if(item_len === 0){
                        items.push(0);
                    } else {
                        items.push(s.substring(0, item_len));
                    }
                }
                inputs[i].witness = items;
            }
        }
        const locktime = little_endian_to_int(s, 4);
        return new Tx(version, inputs, outputs, locktime, segwit);
    }
    encode(force_legacy, sig_index=-1){
       const out = [];
       out.push(int_to_little_endian(this.version, 4));
       if(this.segwit && (!force_legacy)){
           out.push('0001');
       }
       out.push(encode_varint(this.tx_ins.length));
       if(sig_index === -1){
           this.tx_ins.forEach(function(tx_in){
               out.push(tx_in.encode(true));
           });
       } else {
           this.tx_ins.forEach(function(tx_in, index){
               if(sig_index === index){
                   out.push(tx_in.encode(true));
               } else {
                   out.push(tx_in.encode(false));
               }
           });
       }
       out.push(encode_varint(self.tx_outs.length));
       this.tx_outs.forEach(function(tx_out){
            out.push(tx_out.encode());
        });
        if(this.segwit && (!force_legacy)){
            this.tx_ins.forEach(function(tx_in){
                out.push(encode_varint(tx_in.witness.length));
                tx_in.witness.forEach(function(item){
                    if(typeof item === 'number'){
                        out.push(encode_varint(item));
                    } else {
                        out.push(encode_varint(item.length));
                        out.push(item);
                    }
                });
            });
        }
        out.push(int_to_little_endian(this.locktime, 4));
        if(sig_index !== -1){
            out.push(int_to_little_endian(1, 4));
        }
        return out.join('');
    }
    id(){
        const force_legacy = true;
        const tx_id = sha256(sha256(this.encode(force_legacy, -1)));
        return big_to_little_endian(tx_id);
    }
    fee(){
        let input_total = 0, output_total = 0;
        this.tx_ins.forEach(function(tx_in){
            input_total += tx_in.get_value();
        });
        this.tx_outs.forEach(function(tx_out){
            output_total += tx_out.amount
        });

        return input_total-output_total;
    }
    validate(){
        if(this.segwit){
            console.log('can not validate the segwit transaction.')
        }
        if(this.fee() < 0){
            return false;
        }
        let mod_tx_enc, combined, valid;
        this.tx_ins.forEach(function(tx_in, index){
            mod_tx_enc = this.encode(false, index);
            combined = tx_in.script_sig.concate(tx_in.script_pubkey());
            valid = combined.evaluate(mod_tx_enc);
            if(!valid){
                return false;
            }
        });
        return true;
    }
    is_coinbase(){
        const cb_tx = this.tx_ins[0];
        const cb_txid = '0000000000000000';
        if((this.tx_ins.length === 1) && (cb_tx.prev_tx_id === cb_txid) && (cb_tx.tx_index === 0xffffffff)){
            return true;
        } else {
            return false;
        }
    }
    coinbase_height(){
        if(this.is_coinbase()){
            return int_from_little(this.tx_ins[0].script_sig.cmds[0])
        } else {
            return null;
        }
    }
}
class Script {
    constructor(cmds){
        this.cmds = cmds;
    }
    static decode(hex_stream){
        let [length,  s] = decode_varint(hex_stream);
        const cmds = [];
        let count = 0;
        let current, current_byte, data_length, op_code;
        while(count < length){
            current = s.substring(0, 2);
            count += 1;
            current_byte = parseInt(current);
            if(current_byte >= 1 && current_byte <= 75){
                cmds.push(s.substring(2, current_byte*2));
                count += current_byte;
                s = s.slice(2+current_byte*2);
            } else if(current_byte === 76){
                data_length = little_endian_to_int(s.substring(2, 4), 1);
                cmds.push(s.substring(4, data_length*2));
                count += data_length + 1;
                s = s.slice(4+data_length*2);
            } else if(current_byte === 77){
                data_length = little_endian_to_int(s.substring(2, 6), 2);
                cmds.push(s.substring(6, data_length*2));
                count += data_length + 2;
                s = s.slice(6+data_length*2);
            } else {
                op_code = current_byte;
                cmds.push(op_code);
                s = s.slice(2);
            }
        }
        if(count !== length){
            throw new Error('parsing script failed');
        }
        return {
            script_obj: new Script(cmds),
            remaining_str: s,
        }
    }
    encode(){
        let length, result = '';
        this.cmds.forEach(function(cmd){
            if(typeof cmd === 'number'){
                result += int_to_little_endian(cmd, 1);
            } else {
                length = parseInt(cmd.length/2);
                if(length < 75){
                    result += int_to_little_endian(length, 1);
                } else if((length >= 76) && (length <= 255)){
                    result += int_to_little_endian(76, 1);
                    result += int_to_little_endian(length, 1);
                } else if((length >= 256) && (length <= 520)){
                    result += int_to_little_endian(77, 1);
                    result += int_to_little_endian(length, 2);
                } else {
                    throw new Error(`cmd of length ${length} bytes is too long?`);
                }
                result += cmd;
            }
        });
        const total_len = encode_varint(parseInt(result.length/2));
        return total_len + result;
    }
    evaluate(mod_tx_enc){
        if(this.cmds.length !== 7){
            return false;
        }
        const pubkey = this.cmds[1];
        const pubkey_hash = this.cmds[4];
        const cal_pubkey_hash = RIPEMD160(sha256(pubkey));
        if(pubkey_hash !== cal_pubkey_hash){
            return false;
        }
        const sighash_type = this.cmds[0].substring(-1);
        if(sighash_type !== 1){
            return false;
        }
        const der = this.cmds[0].substring(0, -1);
        const sec = this.cmds[1];
        const sig = Signature.decode(der);
        const pk = PublicKey.decode(sec);
        const valid = verify(pk, mod_tx_enc, sig);
        return valid;
    }
}
const ALPHABET_DECODE = '123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz';
function address_to_pkb_hash(address){
    let num = 0n;
    for(let i = 0; i < address.length; i++){
        num *= 58n;
        num += BigInt(ALPHABET_DECODE.indexOf(address[i]));
    }
    const byte_address = (num.toString(16)).padStart(50, '0');
    const checksum = sha256(sha256(byte_address.substring(0, 42)));
    if(byte_address.substring(42) !== checksum.substring(0, 8)){
        const show_alert = 'Address is not correct, Please check again';
        console.log(show_alert);
    }
    const pkb_hash = byte_address.substring(2, 42);
    return pkb_hash;
}
document.getElementById('sender_addr').addEventListener('blur', valSenderAddr);
document.getElementById('prev_tx_id1').addEventListener('blur', valTxid);
document.getElementById('prev_tx_index1').addEventListener('blur', valIndex);
document.getElementById('address1').addEventListener('blur', valAddress);
document.getElementById('amount1').addEventListener('blur', valAmount);
document.getElementById('address2').addEventListener('blur', valAddress);
document.getElementById('amount2').addEventListener('blur', valAmount);
document.getElementById('add_recipient').addEventListener('click', addRecipient);
document.getElementById('remove_recipient').addEventListener('click', removeRecipient);
document.getElementById('add_sender').addEventListener('click', addSender);
document.getElementById('remove_sender').addEventListener('click', removeSender);
document.getElementById('sign').addEventListener('click', VerifyInputs);
const sender_bool = [false, false];
const recipient_bool = [false, false, false, false];
const canSubmit = [false, true, true, sender_bool, recipient_bool];
document.getElementById('sign').disabled = true;
let num_sender = 1, sender_class_counter = 2;
let num_recipient = 2, recipient_class_counter = 4;
const INPUT_CONTENT = [];
const OUTPUT_CONTENT = [];
const SIGN_CONTENT = [];
function valSenderAddr(e){
    valAlphanumeric(e, 'Address', 34, canSubmit, SIGN_CONTENT);
}
function valTxid(e){
    valAlphanumeric(e, 'ID', 64, sender_bool, INPUT_CONTENT);
}
function valIndex(e){
    valNumeric(e, 'Index', sender_bool, INPUT_CONTENT);
}
function valAddress(e){
    valAlphanumeric(e, 'Address', 34, recipient_bool, OUTPUT_CONTENT);
}
function valAmount(e){
    valNumeric(e, 'Amount', recipient_bool, OUTPUT_CONTENT);
}
function valAlphanumeric(e, type, allowed_len, input_bool, input_content){
    const val_length = e.target.value.length;
    const value = e.target.value;
    const classes = e.target.classList;
    const errorElement = e.target.parentElement.nextElementSibling;
    let id = classes[0];
    id = parseInt(id.match(/\d+/)[0]);
    if(val_length === 0){
        input_bool[id] = false;
    } else if(val_length !== allowed_len){
        if(!classes.contains('is-invalid')){
            classes.add('is-invalid');
            errorElement.innerHTML = 
                `<small>The length of ${type} must be ${allowed_len}</small>`;
            if(classes.contains('is-valid')){
                classes.remove('is-valid');
            }
        } else {
            errorElement.innerHTML = 
                `<small>The length of ${type} must be ${allowed_len}</small>`;
        }
        input_bool[id] = false;
    } else if(val_length === allowed_len) {
        if(value.match(/^[a-zA-Z0-9]*$/) === null){
            if(!classes.contains('is-invalid')){
                classes.add('is-invalid');
                errorElement.innerHTML = 
                    '<small>only alphaNumeric characters allowed</small>';
                if(classes.contains('is-valid')){
                    classes.remove('is-valid');
                }
            } else {
                errorElement.innerHTML = 
                    '<small>only alphaNumeric characters allowed</small>';
            }
            input_bool[id] = false;
        } else {
            if(!classes.contains('is-valid')){
                classes.add('is-valid'); 

                if(errorElement.children.length !== 0){
                    errorElement.innerHTML = '';
                }
                if(classes.contains('is-invalid')){
                    classes.remove('is-invalid');
                }
            }
            input_content[id] = value;
            input_bool[id] = true;
        }
    }
    checkSubmit();
}
function valNumeric(e, type, input_bool, input_content){
    const val_length = e.target.value.length;
    let value = e.target.value;
    const classes = e.target.classList;
    const errorElement = e.target.parentElement.nextElementSibling;
    let id = classes[0];
    id = parseInt(id.match(/\d+/)[0]);
    if(val_length === 0){
        if(!classes.contains('is-invalid')){
            classes.add('is-invalid');
            errorElement.innerHTML = 
                '<small>Enter valid Integer</small>';

            if(classes.contains('is-valid')){
                classes.remove('is-valid');
            }
        } else {
            errorElement.innerHTML = 
                '<small>Enter valid Integer</small>';
        }
        input_bool[id] = false;
    } else if(value.indexOf('.') !== -1){
        if(!classes.contains('is-invalid')){
            classes.add('is-invalid');
            errorElement.innerHTML = 
                `<small>${type} must be +ve Integer</small>`;

            if(classes.contains('is-valid')){
                classes.remove('is-valid');
            }
        } else {
            errorElement.innerHTML = 
                `<small>${type} must be +ve Integer</small>`;
        }
        input_bool[id] = false;
    } else if(value.indexOf('-') !== -1){
            if(!classes.contains('is-invalid')){
                classes.add('is-invalid');
                errorElement.innerHTML = 
                    `<small>${type} can not be -ve.</small>`;
    
                if(classes.contains('is-valid')){
                    classes.remove('is-valid');
                }
            } else {
                errorElement.innerHTML = 
                    `<small>${type} can not be -ve.</small>`;
            }
            input_bool[id] = false;
    } else {
        value = parseInt(value);
        if(!classes.contains('is-valid')){
            classes.add('is-valid');
            if(errorElement.children.length !== 0){
                errorElement.innerHTML = '';
            }
            if(classes.contains('is-invalid')){
                classes.remove('is-invalid');
            }
        }
        input_content[id] = value;
        input_bool[id] = true;
    }
    checkSubmit();
}
function checkSubmit(){
    let true_counter = 0;
    canSubmit.forEach(function(element){
        if(Array.isArray(element)){
            element.forEach(function(elem){
                if(elem){
                    true_counter += 1;
                }
            });
        } else {
            if(element){
                true_counter += 1;
            }
        }
    });
    const total_length = canSubmit.length+sender_bool.length+recipient_bool.length-2;
    if(true_counter === total_length){
        document.getElementById('sign').disabled = false;
    } else {
        document.getElementById('sign').disabled = true;
    }
}
function addSender(e){
    num_sender += 1;
    const parent_elem = document.getElementById(`sender${num_sender}`);
    parent_elem.innerHTML = 
        `<label class="output-label mb-1">${num_sender}. Previous Transaction</label>
        <div class="input-group">
            <span class="input-group-text span-color">ID (Hash)</span>
            <input type="text" class="num${sender_class_counter} form-control" id="prev_tx_id${num_sender}" placeholder="9796533c33e46d94a9c1db451758c2b6ecc06e199b91c6515f7fee0e3fc54afc">
        </div>
        <p class="warning"></p>
        <div style="width:50%" class="input-group">
            <span class="input-group-text span-color">Index</span>
            <input type="number" class="num${sender_class_counter+1} form-control" id="prev_tx_index${num_sender}" placeholder="0">
        </div>
        <p class="warning"></p>`;
    sender_class_counter += 2;
    if(num_sender === 2){
        const change_btn_color = document.getElementById('remove_sender');
        change_btn_color.classList.remove('btn-outline-secondary');
        change_btn_color.classList.add('btn-outline-danger');
    }
    const elem = `<div id="sender${num_sender+1}" class="box"></div>`;
    // console.log(elem);
    parent_elem.insertAdjacentHTML('afterend', elem);
    // add eventListener for validation
    const prev_tx_id = document.getElementById(`prev_tx_id${num_sender}`),
        prev_tx_index = document.getElementById(`prev_tx_index${num_sender}`);
    prev_tx_id.addEventListener('blur', valTxid);
    prev_tx_index.addEventListener('blur', valIndex);
    sender_bool.push(false);
    sender_bool.push(false);
    checkSubmit();
    calculateFee();
}
function removeSender(e){
    if(num_sender > 1){
        document.getElementById(`sender${num_sender}`).remove();
        document.getElementById(`sender${num_sender+1}`).id = `sender${num_sender}`;
        num_sender -= 1;
        if(num_sender === 1){
            const change_btn_color = document.getElementById('remove_sender');
            change_btn_color.classList.add('btn-outline-secondary');
            change_btn_color.classList.remove('btn-outline-danger');
        }
        sender_class_counter -= 2;
        sender_bool.pop();
        sender_bool.pop();
        INPUT_CONTENT.pop();
        INPUT_CONTENT.pop();
        checkSubmit();
        calculateFee();
    }
}
function addRecipient(e){
    num_recipient += 1;
    const parent_elem = document.getElementById(`recipient${num_recipient}`);
    parent_elem.innerHTML = 
        `<label class="output-label mb-1">Recipient: ${num_recipient}</label>
        <div class="input-group">
            <span class="input-group-text span-color">Address</span>
            <input type="text" class="num${recipient_class_counter} form-control" id="address${num_recipient}" placeholder="mohjSavDdQYHRYXcS3uS6ttaHP8amyvX78">
        </div>
        <p class="warning"></p>
        <div class="small-box input-group">
            <span class="input-group-text span-color">Amount</span>
            <input type="number" class="num${recipient_class_counter+1} form-control" id="amount${num_recipient}" placeholder="10000 (in satoshi)">
        </div>
        <p class="warning"></p>`;
    recipient_class_counter += 2;
    if(num_recipient === 2){
        const change_btn_color = document.getElementById('remove_recipient');
        change_btn_color.classList.remove('btn-outline-secondary');
        change_btn_color.classList.add('btn-outline-danger');
    }
    const elem = `<div id="recipient${num_recipient+1}" class="box"></div>`;
    parent_elem.insertAdjacentHTML('afterend', elem);
    const address = document.getElementById(`address${num_recipient}`),
            amount = document.getElementById(`amount${num_recipient}`);
    address.addEventListener('blur', valAddress);
    amount.addEventListener('blur', valAmount);
    recipient_bool.push(false);
    recipient_bool.push(false);
    checkSubmit();
    calculateFee();
}

function removeRecipient(e){
    if(num_recipient > 1){
        document.getElementById(`recipient${num_recipient}`).remove();
        document.getElementById(`recipient${num_recipient+1}`).id = `recipient${num_recipient}`;
        num_recipient -= 1;
        if(num_recipient === 1){
            const change_btn_color = document.getElementById('remove_recipient');
            change_btn_color.classList.remove('btn-outline-danger');
            change_btn_color.classList.add('btn-outline-secondary');
        }
        recipient_class_counter -= 2;
        recipient_bool.pop();
        recipient_bool.pop();
        if(OUTPUT_CONTENT.length > 2){
            OUTPUT_CONTENT.pop();
            OUTPUT_CONTENT.pop();
        }
        checkSubmit();
        calculateFee();
    }
}
CAL_ADDRESS_TRACKER = [true, false, false];
document.getElementById('master_privkey').addEventListener('blur', (e) => {
    if(!document.getElementById('master_privkey').readOnly){
        const classes = e.target.classList;
        const errorElement = e.target.parentElement.nextElementSibling;
        let get_private_key = e.target.value;
        const id = parseInt(classes[0].match(/\d+/)[0]);
        if(get_private_key.length === 0){
            canSubmit[id] = false;
            CAL_ADDRESS_TRACKER[id] = false;
            if(!classes.contains('is-invalid')){
                classes.add('is-invalid');
                errorElement.innerHTML = 
                    '<small>Enter valid Integer</small>';

                if(classes.contains('is-valid')){
                    classes.remove('is-valid');
                }
            } else {
                errorElement.innerHTML = 
                    '<small>Enter valid Integer</small>';
            }
        } else if(get_private_key.match(/\d+/)[0].length !== get_private_key.length){
            if(!classes.contains('is-invalid')){
                classes.add('is-invalid');
                errorElement.innerHTML = 
                    '<small>Not a +ve number</small>';
    
                if(classes.contains('is-valid')){
                    classes.remove('is-valid');
                }
            }
            canSubmit[id] = false;
            CAL_ADDRESS_TRACKER[id] = false;
        } else {
            if(!classes.contains('is-valid')){
                classes.add('is-valid'); 
                if(errorElement.children.length !== 0){
                    errorElement.innerHTML = '';
                }
                if(classes.contains('is-invalid')){
                    classes.remove('is-invalid');
                }
            }
            CAL_ADDRESS_TRACKER[id] = true;
            canSubmit[id] = true;
            SIGN_CONTENT[id] = BigInt(get_private_key.match(/\d+/)[0]);
        }
        checkSubmit();
        checkAddress();
    }
});

document.getElementById('master_seed').addEventListener('blur', (e) => {
    if(!document.getElementById('master_seed').readOnly){
        const val_length = e.target.value.length;
        let value = e.target.value;
        const classes = e.target.classList;
        const errorElement = e.target.parentElement.nextElementSibling;
        let id = classes[0];
        id = parseInt(id.match(/\d+/)[0]);
        if(val_length === 0){
            if(!classes.contains('is-invalid')){
                classes.add('is-invalid');
                errorElement.innerHTML = 
                    '<small>Enter valid Integer</small>';

                if(classes.contains('is-valid')){
                    classes.remove('is-valid');
                }
            } else {
                errorElement.innerHTML = 
                    '<small>Enter valid Integer</small>';
            }
            canSubmit[id] = false;
            CAL_ADDRESS_TRACKER[id] = false;
        } else if(value.indexOf('.') !== -1){
            if(!classes.contains('is-invalid')){
                classes.add('is-invalid');
                errorElement.innerHTML = 
                    `<small>must be +ve Integer</small>`;

                if(classes.contains('is-valid')){
                    classes.remove('is-valid');
                }
            } else {
                errorElement.innerHTML = 
                    `<small>must be +ve Integer</small>`;
            }
            canSubmit[id] = false;
            CAL_ADDRESS_TRACKER[id] = false;
        } else if(value.indexOf('-') !== -1){
            if(!classes.contains('is-invalid')){
                classes.add('is-invalid');
                errorElement.innerHTML = 
                    `<small>Seed can not be -ve.</small>`;
    
                if(classes.contains('is-valid')){
                    classes.remove('is-valid');
                }
            } else {
                errorElement.innerHTML = 
                    `<small>Seed can not be -ve.</small>`;
            }
            canSubmit[id] = false;
            CAL_ADDRESS_TRACKER[id] = false;
        } else {
            value = parseInt(value);
            if(value >= 0 && value <= (2**32-1)) {
                if(!classes.contains('is-valid')){
                    classes.add('is-valid'); 
                    if(errorElement.children.length !== 0){
                        errorElement.innerHTML = '';
                    }
                    if(classes.contains('is-invalid')){
                        classes.remove('is-invalid');
                    }
                }
                SIGN_CONTENT[id] = value;
                canSubmit[id] = true;
                CAL_ADDRESS_TRACKER[id] = true;
            } else {
                if(!classes.contains('is-invalid')){
                    classes.add('is-invalid');
                    errorElement.innerHTML = 
                        '<small>must be +ve and less than 4294967296</small>';
        
                    if(classes.contains('is-valid')){
                        classes.remove('is-valid');
                    }
                } else {
                    errorElement.innerHTML = 
                        '<small>must be +ve and less than 4294967296</small>';
                }
                canSubmit[id] = false;
                CAL_ADDRESS_TRACKER[id] = false;
            }
        }
        checkSubmit();
        checkAddress();
    }
});
function checkAddress(){
    let true_counter = 0;
    CAL_ADDRESS_TRACKER.forEach(element => {
        if(element){
            true_counter += 1;
        }
    });
    if(true_counter === CAL_ADDRESS_TRACKER.length){
        document.getElementById('cal_address_btn').disabled = false;
    } else {
        document.getElementById('cal_address_btn').disabled = true;
    }
}
function calculateFee(){
    const min_fee = (4 + 1 + num_sender*147 + 1 + num_recipient*34 + 4);
    const rounded_fee = min_fee + (50-min_fee%50);
    let sats_per_byte = rounded_fee/min_fee;
    sats_per_byte = sats_per_byte.toFixed(2);
    document.getElementById('fee').value = `${rounded_fee} Satoshi, ${sats_per_byte}sats/byte`;
}
function VerifyInputs(e){
    e.target.innerHTML = `<span class="spinner-border spinner-border-sm" role="status"></span>
                            Verifying...`;
    e.target.disabled = true;
    const master_key = BigInt(document.getElementById('master_privkey').value);
    const seed = parseInt(document.getElementById('master_seed').value);
    let calHDKEY;
    if(seed === 0){
        calHDKEY = master_key;
    } else {
        calHDKEY = calc_HD_key(seed, master_key);
        calHDKEY = BigInt('0x'+calHDKEY);
    }
    const calculated_addr = PublicKey.from_sk(calHDKEY).bitcoin_address('test', true, true);
    if(calculated_addr !== SIGN_CONTENT[0]){
        const addr_error = document.getElementById('sender_addr');
        addr_error.classList.remove('is-valid');
        addr_error.classList.add('is-invalid');
        addr_error.parentElement.nextElementSibling.innerHTML = 
            '<small>Address mismatch, Incorrect Sender address or Master PrivateKey/Seed.</small>'; 
    }
    let total_output_amount = 0;
    for(let i = 0; i < OUTPUT_CONTENT.length; i += 2){
        total_output_amount += OUTPUT_CONTENT[i+1];
    }
    let total_input_amount = 0;
    let ptxid, show_output;
    function getTx(elem_counter, url, txIndex){
        return new Promise((resolve, reject) => {
            fetch(url, {method: 'GET', redirect: 'follow'})
            .then(response => {
                if(!response.ok){
                    response.text().then(() => {
                        ptxid = document.getElementById(`prev_tx_id${elem_counter}`);
                        ptxid.classList.remove('is-valid');
                        ptxid.classList.add('is-invalid');
                        show_output = ptxid.parentElement.nextElementSibling;
                        show_output.innerHTML = '<small>Transaction not Found on Blockchain</small>';
                        document.getElementById('sign').innerText = 'Verify & Sign';
                    });
                    return Promise.reject();
                }
                return response.json();
            })
            .then(result => {
                let show_output;
                if(result.vout[txIndex] === undefined){
                    let ptxidx = document.getElementById(`prev_tx_index${elem_counter}`);
                    ptxidx.classList.remove('is-valid');
                    ptxidx.classList.add('is-invalid');
                    show_output = ptxidx.parentElement.nextElementSibling;
                    show_output.innerHTML = '<small>Index does not exist.</small>';
                    document.getElementById('sign').innerText = 'Verify & Sign'
                } else if(result.vout[txIndex].scriptpubkey_address !== SIGN_CONTENT[0]){
                    let sen_addr = document.getElementById('sender_addr');
                    sen_addr.classList.remove('is-valid');
                    sen_addr.classList.add('is-invalid');
                    show_output = sen_addr.parentElement.nextElementSibling;
                    show_output.innerHTML = '<small>Address mismatch, Please check the Sender address or Tx Index</small>';
                    document.getElementById('sign').innerText = 'Verify & Sign'
                } else{
                    total_input_amount += result.vout[txIndex].value;
                }
                resolve();
            })
            .catch(error => {
                if(error !== undefined){
                    const output_area = document.getElementById('info_block');
                    output_area.innerHTML = `<h3 style="color: #AF0606">Network Error</h3><p>${error}</p>`;
                    document.getElementById('sign').innerText = 'Verify & Sign';
                }
            });
        })
    }
    const txRequest = [];
    id_grab_counter = 0;
    for(let i = 0; i < INPUT_CONTENT.length; i += 2){
        id_grab_counter += 1;
        txRequest.push(getTx(id_grab_counter, `https://blockstream.info/testnet/api/tx/${INPUT_CONTENT[i]}`, INPUT_CONTENT[i+1]));
    }
    Promise.all(txRequest)
        .then(() => {
            const calfee = total_input_amount-total_output_amount;
            const output_area = document.getElementById('info_block');
            if(calfee < 0){
                output_area.innerHTML = `<h3 style="color: #AF0606;">Invalid: Overspending ${Math.abs(calfee)} Satoshi</h3>
                                        <p style="font-weight: bold; font-size: 1.5rem">Only have ${total_input_amount} satoshi, spending ${total_output_amount} satoshi</p>`;
                document.getElementById('sign').innerText = 'Verify & Sign';
            } else {
                const min_fee = parseInt(document.getElementById('fee').value);
                if(calfee < min_fee){
                    output_area.innerHTML = `<h3 style="color: #AF0606;">Invalid: Fee less than Minimum recommended fee.</h3>
                                                <p style="font-weight: bold; font-size: 1.5rem">Subtract ${min_fee-calfee} satoshi from Any of the Amount field.</p>`;
                   
                    document.getElementById('sign').innerText = 'Verify & Sign';
                } else {
                    document.getElementById('sign').innerText = 'Verify & Sign';
                    Sign(e);
                }
            }
        })
}
function Sign(e){
    const SENDER = [];
    let TX_IN
    const IN_PUBKEY = address_to_pkb_hash(SIGN_CONTENT[0]);
    const source_script = new Script([118, 169, IN_PUBKEY, 136, 172]);
    for(let i = 0; i < INPUT_CONTENT.length; i += 2){
        TX_IN = new TxIn(prev_tx_id=INPUT_CONTENT[i],
                        tx_index=INPUT_CONTENT[i+1],
                        script_sig=null,
        );
        TX_IN.script_sig = source_script;
        SENDER.push(TX_IN);
    }
    const RECIPIENTS = [];
    let TX_OUT, PKB_HASH, OUT_SCRIPT;
    for(let i = 0; i < OUTPUT_CONTENT.length; i += 2){
        PKB_HASH = address_to_pkb_hash(OUTPUT_CONTENT[i]);
        TX_OUT = new TxOut(amount=OUTPUT_CONTENT[i+1],script_pubkey=null);
        OUT_SCRIPT = new Script([118, 169, PKB_HASH, 136, 172]);
        TX_OUT.script_pubkey = OUT_SCRIPT;

        RECIPIENTS.push(TX_OUT);
    }
    const TX = new Tx(version=1,
                        tx_ins=SENDER,
                        tx_outs=RECIPIENTS,
                        locktime=0,
                        segwit=false,
    );
    const master_key = BigInt(document.getElementById('master_privkey').value);
    const seed = parseInt(document.getElementById('master_seed').value);
    let calHDKEY;
    if(seed === 0){
        calHDKEY = master_key;
    } else {
        calHDKEY = calc_HD_key(seed, master_key);
        calHDKEY = BigInt('0x'+calHDKEY);
    }
    const pubkey_bytes = PublicKey.from_sk(calHDKEY).encode(true, false);
    let message, SIG, SIG_hex, sig_byte_and_type, SCRIPT_SIG;
    for(let i = 0; i < SENDER.length; i++){
        message = TX.encode(true, i);
        SIG = sign(calHDKEY, message);
        SIG_hex = SIG.encode();
        sig_byte_and_type = SIG_hex + '01';
        SCRIPT_SIG = new Script([sig_byte_and_type, pubkey_bytes]);
        TX.tx_ins[i].script_sig = SCRIPT_SIG;
    }
    const SIGNED_TX = TX.encode(true);
    let TX_ID = sha256(sha256(SIGNED_TX));
    TX_ID = big_to_little_endian(TX_ID);
    const output_area = document.getElementById('info_block');
    output_area.innerHTML =
    `<h3 style="color: rgb(33, 37, 41);" class="box">Broadcast raw transaction (hex)</h3>
        <div id="output_tx" class="input-group box mb-3">
        <textarea style="color: rgb(33, 37, 41);" class="form-control form-control-sm" rows="6" disabled>${SIGNED_TX}</textarea>
    </div>
    <button type="button" id="broadcast" class="btn btn-success mb-3">BroadCast</button>`;
    document.getElementById('broadcast').addEventListener('click', function(e){
        e.target.innerHTML = `<span class="spinner-border spinner-border-sm" role="status"></span>
                            BroadCasting...`;
        e.target.disabled = true;
        let myHeaders = new Headers();
        myHeaders.append("Content-Type", "text/plain");
        let requestOptions = {method: 'POST', headers: myHeaders, mode: 'cors', redirect: 'follow', body: SIGNED_TX};
        fetch('https://blockstream.info/testnet/api/tx', requestOptions)
            .then(response => {
                if(!response.ok){
                    response.text().then(error => {
                        output_area.innerHTML = `<h3 style="color: #AF0606">Invalid Transaction</h3><p>${error}</p>`;
                        document.getElementById('sign').innerText = 'Verify & Sign';
                    });
                    return Promise.reject();
                }
                return response.text();
            })
            .then(result => {
                output_area.previousElementSibling.style.display = "none";
                e.target.remove();
                output_area.innerHTML = `<h3 style="color: green">Congratulations: Transaction Successful.</h3>
                    <p>Wait 5-10sec for link to be active.
                    <a href="https://www.blockchain.com/btc-testnet/tx/${result}" target="_blank">Check Transaction Status</a></p>`;
                document.getElementById('sign').innerText = 'Verify & Sign';
            })
            .catch(error => {
                if(error !== undefined){
                    const output_area = document.getElementById('info_block');
                    output_area.innerHTML = `<h3 style="color: #AF0606">Network Error</h3><p>${error}</p>`;
                    document.getElementById('sign').innerText = 'Verify & Sign';
                }
            });
    });
}
