package main

import (
	"fmt"
	"math/rand"
)

func setToRandom(a []uint64) {
	for i := range a {
		a[i] = rand.Uint64()
	}
}

func getRandomBytes(size int) []byte {
	a := make([]byte, size)
	for i := range a {
		a[i] = byte(rand.Int())
	}
	return a
}

func printU64(a uint64) {
	fmt.Print("(UInt64.uint64_of_Z_mod ")
	fmt.Print(a)
	fmt.Print(")%Z")
}

func printVec(a []uint64) {
	for _, x := range a {
		fmt.Print("  ")
		printU64(x)
		fmt.Println()
	}
}
