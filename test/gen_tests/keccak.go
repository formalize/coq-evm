package main

import (
	"encoding/hex"
	"fmt"

	"golang.org/x/crypto/sha3"
)

func printSha3Test(index, size int) {
	data := getRandomBytes(size)
	hash := sha3.Sum256(data)

	fmt.Println("(*********************************)")
	fmt.Print("Lemma test_sha3_")
	fmt.Print(index)
	fmt.Println(":")

	fmt.Print("Keccak.sha3_256_hex (bytes_of_hex \"")
	fmt.Print(hex.EncodeToString(data))
	fmt.Println("\" eq_refl)")

	fmt.Println(" =")

	fmt.Print("\"")
	fmt.Print(hex.EncodeToString(hash[:]))
	fmt.Println("\".")

	fmt.Println("Proof. trivial. Qed.")

	//////////////////////////////////////////////////
	fmt.Println()

	fmt.Print("Lemma test_keccak_")
	h := sha3.NewLegacyKeccak256()
	h.Write(data)
	hashKeccak := h.Sum(nil)

	fmt.Print(index)
	fmt.Println(":")

	fmt.Print("Keccak.keccak_256_hex (bytes_of_hex \"")
	fmt.Print(hex.EncodeToString(data))
	fmt.Println("\" eq_refl)")

	fmt.Println(" =")

	fmt.Print("\"")
	fmt.Print(hex.EncodeToString(hashKeccak[:]))
	fmt.Println("\".")

	fmt.Println("Proof. trivial. Qed.")
}

func printSha3Tests() {
	fmt.Println("From Coq Require Import String.")
	fmt.Println("From EVM Require Import Nibble.")
	fmt.Println("From EVM Require Keccak.")
	fmt.Println("Open Scope string_scope.")
	counter := 0
	for size := 0; size < 200; size++ {
		fmt.Println("(***** size: ", size, " *****)")
		n_iter := 1
		for iter := 0; iter < n_iter; iter++ {
			counter++
			printSha3Test(counter, size)
		}
	}
}
