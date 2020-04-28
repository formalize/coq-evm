package main

import (
	"fmt"
	"math/rand"

	"../../3rdparty/blake2b"
)

func printBlakeTest(index, rounds int) {
	var h [8]uint64
	setToRandom(h[:])

	var m [16]uint64
	setToRandom(m[:])

	var c [2]uint64
	setToRandom(c[:])

	var f bool = rand.Int()&1 != 0

	fmt.Println("(*********************************)")
	fmt.Print("Lemma test")
	fmt.Print(index)
	fmt.Println(":")
	fmt.Println("let h := Vec8.Vec8")
	printVec(h[:])

	fmt.Println("in let m := Vec16.Vec16")
	printVec(m[:])

	fmt.Print("in let c0 := ")
	printU64(c[0])
	fmt.Println()

	fmt.Print("in let c1 := ")
	printU64(c[1])
	fmt.Println()

	fmt.Print("in let f := ")
	if f {
		fmt.Println("true")
	} else {
		fmt.Println("false")
	}
	fmt.Print("in BLAKE2b.F h m c0 c1 f ")
	printU64(uint64(rounds))
	fmt.Println()

	blake2b.F(&h, m, c, f, uint32(rounds))
	fmt.Println("= Vec8.Vec8")
	printVec(h[:])
	fmt.Println(". Proof. trivial. Qed.")
}

func printBlakeTests() {
	fmt.Println("From Coq Require Import ZArith.")
	fmt.Println("From EVM Require UInt64 BLAKE2b.")
	fmt.Println()
	counter := 0
	for rounds := 0; rounds < 25; rounds++ {
		fmt.Println("(***** F rounds: ", rounds, " *****)")
		for iter := 0; iter < 10; iter++ {
			counter++
			printBlakeTest(counter, rounds)
		}
	}
}
