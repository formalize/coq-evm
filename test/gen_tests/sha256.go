package main

import (
	"crypto/sha256"
	"encoding/hex"
	"fmt"
)

func printSha256Test(index, size int) {
	data := getRandomBytes(size)
	hash := sha256.Sum256(data)

	fmt.Println("(*********************************)")
	fmt.Print("Lemma test")
	fmt.Print(index)
	fmt.Println(":")

	fmt.Print("SHA256.sha256_hex (bytes_of_hex \"")
	fmt.Print(hex.EncodeToString(data))
	fmt.Println("\" eq_refl)")

	fmt.Println(" =")

	fmt.Print("\"")
	fmt.Print(hex.EncodeToString(hash[:]))
	fmt.Println("\".")

	fmt.Println("Proof. trivial. Qed.")
}

func printSha256Tests() {
	fmt.Println("From Coq Require Import String.")
	fmt.Println("From EVM Require Import Nibble.")
	fmt.Println("From EVM Require SHA256.")
	fmt.Println("Open Scope string_scope.")
	counter := 0
	for size := 0; size < 200; size++ {
		fmt.Println("(***** size: ", size, " *****)")
		n_iter := 1
		for iter := 0; iter < n_iter; iter++ {
			counter++
			printSha256Test(counter, size)
		}
	}
}
