package main

import (
	"encoding/hex"
	"fmt"

	"golang.org/x/crypto/ripemd160"
)

func printRipemd160Test(index, size int) {
	data := getRandomBytes(size)
	h := ripemd160.New()
	h.Write(data)
	hash := h.Sum(nil)

	fmt.Println("(*********************************)")
	fmt.Print("Lemma test")
	fmt.Print(index)
	fmt.Println(":")

	fmt.Print("RIPEMD160.ripemd160_hex (bytes_of_hex \"")
	fmt.Print(hex.EncodeToString(data))
	fmt.Println("\" eq_refl)")

	fmt.Println(" =")

	fmt.Print("\"")
	fmt.Print(hex.EncodeToString(hash[:]))
	fmt.Println("\".")

	fmt.Println("Proof. trivial. Qed.")
}

func printRipemd160Tests() {
	fmt.Println("From Coq Require Import String.")
	fmt.Println("From EVM Require Import Nibble.")
	fmt.Println("From EVM Require RIPEMD160.")
	fmt.Println("Open Scope string_scope.")
	counter := 0
	for size := 0; size < 200; size++ {
		fmt.Println("(***** size: ", size, " *****)")
		n_iter := 1
		for iter := 0; iter < n_iter; iter++ {
			counter++
			printRipemd160Test(counter, size)
		}
	}
}
