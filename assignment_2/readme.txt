In this homework, you will figure out how to break a vulnerable implementation of RSA using dynamic instrumentation with the help of PIN tool. RSA (Rivest–Shamir–Adleman) cryptosystem is a family of public-key cryptosystems, one of the oldest and widely used for secure data transmission. 

In RSA-based cryptography, a user's public and private key is based on two large prime numbers chosen at random. The product of the two prime numbers (n) are used to generate private and public key pair (d, e). In order to encrypt a message (M), the public key of the user to which data has to be sent is used. Similarly, the intended user uses its private key and decrypts the message. The security of RSA is related to the difficulty of factoring the product into two individual prime numbers.

Summary of RSA Encryption and Decryption:

1. Key Generation

Before encryption and decryption can occur, RSA requires the generation of a key pair.

-> Choose two large prime numbers: Let these primes be p and  q.

-> Compute the modulus: n=p×q

The value n will be used as part of both the public and private keys.

-> Compute Euler’s Totient Function: ϕ(n)=(p−1)(q−1)

-> Choose the public exponent e: Select an integer  𝑒 such that 1<e<ϕ(n) and gcd(e,ϕ(n))=1

-> Compute the private exponent d: Find d such that d×e≡1(modϕ(n))

Thus d is the modular multiplicative inverse of e modulo ϕ(n).

Finally: Public key is (e,n) and Private key is (d,n). The values p, q, and d must remain secret.

2. RSA Encryption

To encrypt a message, the sender uses the recipient’s public key.

-> Convert the plaintext message M into an integer such that 0≤M<n

-> Compute the ciphertext C using modular exponentiation: C=M^e mod(n)

-> The encrypted message C is then transmitted.

Because only the receiver knows the private key d, no one else can easily recover M.

3. RSA Decryption

The receiver decrypts the ciphertext using their private key.

-> Given ciphertext C, compute: M=C^d mod(n)

This operation recovers the original plaintext integer  M, which can then be converted back to the original message.

4. Why RSA Works

RSA relies on the mathematical property: (M^e)^d ≡ M mod(n) because e×d≡1(modϕ(n))

This relationship ensures that raising the ciphertext to the power d reverses the encryption step.

5. Example (Small Numbers)

For illustration: 
-> p=3,  q=11 
-> n=33 
-> ϕ(n)=20
-> Choose e=3
-> Compute d=7 because 3×7 = 21 ≡ 1(mod20)

-> Public key: (3,33)
-> Private key: (7,33)

If the message M=4:

-> Encryption: C = 4^3mod33 = 64mod33 = 31

-> Decryption: M = 31^7mod33 = 4

The original message is recovered.

In theory it is very hard to break the RSA by factorization, in practice however, the algorithm is as secure as its implementation. One such implementation of RSA which is quiet vulnerable to side channel attacks is square and multiply algorithm. In this implementation, the exponentiation operation is performed using square and multiply operations. For each bit of the key (e or d) the square operation is performed, but the multiply operation is only performed if the bit is equal to 1. This differential path makes it vulnerable to various classes of side channel attacks.

Square and Multiply Algorithm (Base M, Key K):
    result = 1
    for i = msb down to lsb:
        result = square(result)
        if key_bit[i] == 1:
            result = multiply(result, M)
    return result

For a particular bit of the key, the multiply operation is only performed when that bit is 1. This dynamic nature of execution can be leveraged to figure out the key used for encryption or decryption.

You are provided with a 64-bit ELF binary which contains the square and multiply implementation of RSA. Your goal is to extract the 64-bit key used for the decryption operation using PIN tool. To get you started, remember that you can use PIN to figure out what type of instruction is being executed.

If you want to check whether the key you have obtained is correct or not, you can run the program with -a <key> flag. For example, ./prog -a 1234, if the program name is "prog" and your key is 1234. This will check the decryption output using your key with the decryption output with the embedded secret key. If your key is correct, "Your Key is Correct" message will be printed, otherwise "Wrong Key" will be printed. The given binary is compiled as 64-bit executable, so make sure that your PIN tool is compatible with 64-bit binary. We will evaluate your implementation using different secret key, so ensure that no values are hardcoded.

Make sure to write your implementation such that it generates a text file named "key.txt" containing only one line, the extracted key in decimal representation. The final submission should contain the source code of your PIN tool, compilation instruction, any additional scripts (used to generate the output file containing the extracted key) and instructions on how to use them.