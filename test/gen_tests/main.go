package main

import (
	"log"
	"math/rand"
	"os"
	"time"
)

func printTests(path string, dump func()) {
	stdout := os.Stdout

	file, err := os.Create(path)
	if err != nil {
		log.Fatal(err)
	}
	os.Stdout = file
	dump()
	file.Close()

	os.Stdout = stdout
}

func main() {
	rand.Seed(time.Now().UnixNano())

	printTests("TestBlake.v", printBlakeTests)
	printTests("TestSHA256.v", printSha256Tests)
	printTests("TestRIPEMD160.v", printRipemd160Tests)
	printTests("TestKeccak.v", printSha3Tests)
}
