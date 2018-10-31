package main

import (
	"github.com/truechain/truechain-engineering-code/crypto/sha3"
)
import "C"
import "io"
const		DATALENGTH   = 2048
const		PMTSIZE	 =	4
const     	TBLSIZE	 =	16
const		HEADSIZE	 =	32
const		DGSTSIZE	 =	32
const		UPDATABLOCKLENGTH  = 12000
const		STARTUPDATENUM = 10240


func genLookupTable(plookup []uint64, ptable []uint32 ) int {
	lktWz := uint32(DATALENGTH / 64)
	lktSz := uint32(DATALENGTH)*lktWz

	//idx := 0
	for k := 0; k < TBLSIZE; k++ {

		plkt := uint32(k)*lktSz

		for x := 0; x < DATALENGTH; x++ {

			for y := 0; y < PMTSIZE; y++ {
				val := ptable[k * DATALENGTH * PMTSIZE + x * PMTSIZE + y]
				if val == 0xFFF	{
					continue;
				}
				vI := val / 64
				vR := val % 64
				plookup[plkt + vI] |= 1 << vR
			}
			plkt += lktWz
		}
	}
	return 0
}

func xor64(val uint64) int{
	var r int = 0
	for k := 0; k < 64; k++ {
		r ^= int(val & 0x1)
		val = val >> 1
	}
	return r
}

func muliple( input []uint64,  prow []uint64) uint{
	var r int = 0
	for k := 0; k < 32; k++	{
		if input[k] != 0 && prow[k] != 0 {
			r ^= xor64(input[k] & prow[k])
		}
	}

	return uint(r)
}

func  MatMuliple( input []uint64,  output []uint64, pmat []uint64) int{
	prow := pmat[:]
	var point uint = 0

	for k := 0; k < 2048; k++	{
		kI := k / 64
		kR := k % 64
		var temp uint
		temp = muliple(input[:], prow[point:])

		output[kI] |= (uint64(temp) << uint(kR))
		point += 32
	}

	return 0
}


func shift2048( in []uint64,  sf int) int{
	var sfI int = sf / 64
	var sfR int = sf % 64
	var mask uint64 = (uint64(1) << uint(sfR)) - 1
	var bits int = (64 - sfR)
	var res uint64
	if sfI == 1 {
		val := in[0]
		for k := 0; k < 31; k++ {
			in[k] = in[k + 1]
		}
		in[31] = val
	}
	res = (in[0] & mask) << uint(bits)
	for k := 0; k < 31; k++ {
		var val uint64 = (in[k + 1] & mask) << uint(bits)
		in[k] = (in[k] >> uint(sfR)) + val
	}
	in[31] = (in[31] >> uint(sfR)) + res
	return 0
}


func scramble( permute_in []uint64, plookup []uint64) int{
	var ptbl []uint64
	var permute_out [32]uint64
	for k := 0; k < 64; k++	{

		sf := int(permute_in[0] & 0x7f)
		bs := int(permute_in[31] >> 60)

		ptbl = plookup[bs * 2048 * 32:]

		MatMuliple(permute_in[:], permute_out[:], ptbl[:])
		shift2048(permute_out[:], sf)

		for k := 0; k < 32; k++ {
			permute_in[k] = permute_out[k]
			permute_out[k] = 0
		}
	}
	return 0
}


func byteReverse( sha512_out []byte) int{
	for k := 0; k < 32; k++ {
		temp := sha512_out[k]
		sha512_out[k] = sha512_out[63 - k]
		sha512_out[63 - k] = temp
	}

	return 0
}
//export fchainmining
func fchainmining( plookup []uint64, header []byte, nonce uint64) ([]byte, []byte){
	var seed [64]byte
	//32
	output := make([]byte, DGSTSIZE)

	val0 := uint32(nonce & 0xFFFFFFFF)
	val1 := uint32(nonce >> 32)

	//4
	for  k:= 3; k >= 0; k--	{
		seed[k] = byte(val0) & 0xFF
		val0 >>= 8
	}
	//4
	for k := 7; k >= 4; k--	{
		seed[k] = byte(val1) & 0xFF
		val1 >>= 8
	}
     //32
	dgst := make([]byte, DGSTSIZE)

	//8-40
	for k := 0; k < HEADSIZE; k++	{
		seed[k+8] = header[k]
	}

	sha512 := makeHasher(sha3.New512())
	var sha512_out [64]byte

	sha512(sha512_out[:],seed[:])
	byteReverse(sha512_out[:])
	var permute_in [32]uint64

	for k := 0; k < 8; k++	{
		for x := 0; x < 8; x++	{
			var sft int= x * 8
			val := (uint64(sha512_out[k*8+x]) << uint(sft))
			permute_in[k] += val
		}
	}
	for k := 1; k < 4; k++	{
		for x := 0; x < 8; x++ {
			permute_in[k * 8 + x] = permute_in[x]
		}
	}

	scramble(permute_in[:], plookup[:])

	var dat_in [256]byte
	for k := 0; k < 32; k++	{
		val := permute_in[k]
		for x := 0; x < 8; x++	{
			dat_in[k * 8 + x] = byte(val & 0xFF)
			val = val >> 8
		}
	}

	for k := 0; k < 64; k++	{
		var temp byte
		temp = dat_in[k * 4];
		dat_in[k * 4] = dat_in[k * 4 + 3];
		dat_in[k * 4 + 3] = temp;
		temp = dat_in[k * 4 + 1];
		dat_in[k * 4 + 1] = dat_in[k * 4 + 2];
		dat_in[k * 4 + 2] = temp;
	}


	sha256 := makeHasher(sha3.New256())

	sha256(output, dat_in[:])
	// reverse byte
	for k := 0; k < DGSTSIZE; k++	{
		dgst[k] = output[k];
	}

	return  dgst, dgst
}
type hasher func(dest []byte, data []byte)
type Hash interface {
	// Write (via the embedded io.Writer interface) adds more data to the running hash.
	// It never returns an error.
	io.Writer

	// Sum appends the current hash to b and returns the resulting slice.
	// It does not change the underlying hash state.
	Sum(b []byte) []byte

	// Reset resets the Hash to its initial state.
	Reset()

	// Size returns the number of bytes Sum will return.
	Size() int

	// BlockSize returns the hash's underlying block size.
	// The Write method must be able to accept any amount
	// of data, but it may operate more efficiently if all writes
	// are a multiple of the block size.
	BlockSize() int
}

// Hash32 is the common interface implemented by all 32-bit hash functions.
type Hash32 interface {
	Hash
	Sum32() uint32
}

// Hash64 is the common interface implemented by all 64-bit hash functions.
type Hash64 interface {
	Hash
	Sum64() uint64
}

func makeHasher(h Hash) hasher {
	return func(dest []byte, data []byte) {
		h.Write(data)
		h.Sum(dest[:0])
		h.Reset()
	}
}

func main() {//main函数是必须的 有main函数才能让cgo编译器去把包编译成C的库
}