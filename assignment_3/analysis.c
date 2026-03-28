#include <stdio.h>
#include <string.h>
#include <openssl/aes.h>
// #include "AES_code.c"
#include "AES_code_solution.c"
#include <signal.h>

#define BLOCK_SIZE 16


volatile int running = 1;
void handler(int x){
    running = 0;
}

int main() {

    /* -------- FIXED 128-bit KEY -------- */
    unsigned char key[BLOCK_SIZE] = {
        0x10, 0x11, 0x22, 0x33,
        0x44, 0x55, 0x66, 0x77,
        0x88, 0x99, 0xaa, 0xbb,
        0xcc, 0xdd, 0xee, 0xff
    };

    unsigned char plaintext[BLOCK_SIZE];
    unsigned char ciphertext[BLOCK_SIZE];
    char hex[33];

    FILE *fin = fopen("plaintext.txt", "r");
    FILE *fout = fopen("ciphertext.txt", "w");

    if (!fin || !fout) {
        printf("File open error\n");
        return 1;
    }

    AES_KEY enc_key;
    AES_set_encrypt_key(key, 128, &enc_key);

    /* -------- READ PLAINTEXT LINE BY LINE -------- */
    while (fscanf(fin, "%32s", hex) == 1) {

        /* Convert hex string to bytes */
        for (int i = 0; i < BLOCK_SIZE; i++) {
            sscanf(&hex[2*i], "%2hhx", &plaintext[i]);
        }

        asm volatile(".rept 20; nop; .endr" ::: "memory");

        /* -------- Encryption -------- */
        AES_code(plaintext, ciphertext, &enc_key);

        asm volatile(".rept 20; nop; .endr" ::: "memory");

        /* -------- WRITE CIPHERTEXT -------- */
        for (int i = 0; i < BLOCK_SIZE; i++) {
            fprintf(fout, "%02x", ciphertext[i]);
        }
        fprintf(fout, "\n");
    }

    fclose(fin);
    fclose(fout);

    printf("Encryption Done\n");
    return 0;
}

