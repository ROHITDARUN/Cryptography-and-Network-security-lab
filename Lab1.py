"""
Classical Ciphers Toolkit
==========================
Implements Caesar, Vigenere, Playfair, and Hill ciphers with encryption,
decryption, validation, cryptanalysis tools, an interactive CLI, and an
automated test suite.

Run this file directly to launch the interactive menu:
    python classical_ciphers.py

Run the automated test suite only:
    python classical_ciphers.py --test
"""

import sys
import math
from math import gcd
from collections import Counter

ALPHABET_SIZE = 26

# Standard English letter frequencies (percent), used for frequency analysis
ENGLISH_FREQ = {
    'A': 8.17, 'B': 1.49, 'C': 2.78, 'D': 4.25, 'E': 12.70, 'F': 2.23,
    'G': 2.02, 'H': 6.09, 'I': 6.97, 'J': 0.15, 'K': 0.77, 'L': 4.03,
    'M': 2.41, 'N': 6.75, 'O': 7.51, 'P': 1.93, 'Q': 0.10, 'R': 5.99,
    'S': 6.33, 'T': 9.06, 'U': 2.76, 'V': 0.98, 'W': 2.36, 'X': 0.15,
    'Y': 1.97, 'Z': 0.07,
}


# ======================================================================
# Helper Functions
# ======================================================================

def _extended_gcd(a: int, b: int):
    if a == 0:
        return b, 0, 1
    g, x1, y1 = _extended_gcd(b % a, a)
    x = y1 - (b // a) * x1
    y = x1
    return g, x, y


def mod_inverse(a: int, m: int) -> int:
    """Compute modular inverse of a under modulo m using Extended Euclid."""
    a = a % m
    if gcd(a, m) != 1:
        raise ValueError(f"No modular inverse exists for {a} mod {m} "
                          f"(gcd={gcd(a, m)} != 1)")
    g, x, _ = _extended_gcd(a, m)
    return x % m


def clean_text(text: str, keep_spaces: bool = False) -> str:
    """Strip non-alphabetic characters, uppercase everything."""
    if keep_spaces:
        return "".join(c.upper() for c in text if c.isalpha() or c == " ")
    return "".join(c.upper() for c in text if c.isalpha())


# ======================================================================
# Generic Matrix helper (used by Hill cipher and cryptanalysis)
# ======================================================================

class MatrixMod:
    """Utility functions for square matrices under modulo m."""

    def __init__(self, m: int = ALPHABET_SIZE):
        self.m = m

    def determinant(self, matrix):
        n = len(matrix)
        if n == 1:
            return matrix[0][0]
        if n == 2:
            return matrix[0][0] * matrix[1][1] - matrix[0][1] * matrix[1][0]
        det = 0
        for c in range(n):
            minor = [row[:c] + row[c + 1:] for row in matrix[1:]]
            det += ((-1) ** c) * matrix[0][c] * self.determinant(minor)
        return det

    def cofactor_matrix(self, matrix):
        n = len(matrix)
        cof = [[0] * n for _ in range(n)]
        for i in range(n):
            for j in range(n):
                minor = [row[:j] + row[j + 1:]
                         for k, row in enumerate(matrix) if k != i]
                cof[i][j] = ((-1) ** (i + j)) * self.determinant(minor)
        return cof

    def inverse(self, matrix):
        n = len(matrix)
        det = self.determinant(matrix) % self.m
        if gcd(det, self.m) != 1:
            raise ValueError(
                f"Matrix not invertible mod {self.m} "
                f"(det={det}, gcd(det,{self.m})={gcd(det, self.m)} != 1)."
            )
        det_inv = mod_inverse(det, self.m)
        cof = self.cofactor_matrix(matrix)
        adj = [[cof[j][i] for j in range(n)] for i in range(n)]  # transpose
        return [[(det_inv * adj[i][j]) % self.m for j in range(n)]
                for i in range(n)]

    def multiply(self, A, B):
        """Multiply matrix A (r x k) by matrix B (k x c), result mod m."""
        r, k, c = len(A), len(B), len(B[0])
        result = [[0] * c for _ in range(r)]
        for i in range(r):
            for j in range(c):
                total = sum(A[i][x] * B[x][j] for x in range(k))
                result[i][j] = total % self.m
        return result

    def multiply_vector(self, matrix, vector):
        n = len(matrix)
        result = [0] * n
        for i in range(n):
            result[i] = sum(matrix[i][j] * vector[j]
                             for j in range(n)) % self.m
        return result


# ======================================================================
# 1. CAESAR CIPHER
# ======================================================================

class CaesarCipher:
    """Monoalphabetic substitution cipher: C = (P + k) mod 26."""

    def __init__(self, key: int):
        self.key = key % ALPHABET_SIZE

    def encrypt(self, plaintext: str) -> str:
        return self._shift(plaintext, self.key)

    def decrypt(self, ciphertext: str) -> str:
        return self._shift(ciphertext, -self.key)

    @staticmethod
    def _shift(text: str, k: int) -> str:
        result = []
        for ch in text:
            if ch.isalpha():
                base = ord('A') if ch.isupper() else ord('a')
                shifted = (ord(ch) - base + k) % ALPHABET_SIZE
                result.append(chr(shifted + base))
            else:
                result.append(ch)  # non-alphabetic chars pass through
        return "".join(result)


# ======================================================================
# 2. VIGENERE CIPHER
# ======================================================================

class VigenereCipher:
    """
    Polyalphabetic substitution cipher: C_i = (P_i + K_(i mod len(key))) mod 26
    Preserves case and passes non-alphabetic characters through unchanged.
    The keystream only advances on alphabetic plaintext characters.
    """

    def __init__(self, key: str):
        key = clean_text(key)
        if not key:
            raise ValueError("Vigenere key must contain at least one letter.")
        self.key = key

    def encrypt(self, plaintext: str) -> str:
        return self._process(plaintext, 1)

    def decrypt(self, ciphertext: str) -> str:
        return self._process(ciphertext, -1)

    def _process(self, text: str, sign: int) -> str:
        result = []
        ki = 0
        klen = len(self.key)
        for ch in text:
            if ch.isalpha():
                base = ord('A') if ch.isupper() else ord('a')
                k = ord(self.key[ki % klen]) - ord('A')
                shifted = (ord(ch) - base + sign * k) % ALPHABET_SIZE
                result.append(chr(shifted + base))
                ki += 1
            else:
                result.append(ch)
        return "".join(result)


# ======================================================================
# 3. PLAYFAIR CIPHER
# ======================================================================

class PlayfairCipher:
    """
    Polygraphic substitution cipher using a 5x5 key-derived grid.
    I and J share a cell. Handles digraph formatting and 'X' padding.
    """

    def __init__(self, key: str):
        self.key = clean_text(key).replace("J", "I")
        self.grid = self._build_grid()
        self.pos = {}
        for r in range(5):
            for c in range(5):
                self.pos[self.grid[r][c]] = (r, c)

    def _build_grid(self):
        seen = set()
        letters = []
        for ch in self.key:
            if ch not in seen and ch != "J":
                seen.add(ch)
                letters.append(ch)
        for ch in "ABCDEFGHIKLMNOPQRSTUVWXYZ":  # no J
            if ch not in seen:
                seen.add(ch)
                letters.append(ch)
        return [letters[i * 5:(i + 1) * 5] for i in range(5)]

    def _prepare_digraphs(self, text: str):
        text = clean_text(text).replace("J", "I")
        digraphs = []
        i = 0
        while i < len(text):
            a = text[i]
            if i + 1 < len(text):
                b = text[i + 1]
                if a == b:
                    digraphs.append((a, "X"))  # split duplicate letters
                    i += 1
                else:
                    digraphs.append((a, b))
                    i += 2
            else:
                digraphs.append((a, "X"))  # odd-length padding
                i += 1
        return digraphs

    def encrypt(self, plaintext: str) -> str:
        digraphs = self._prepare_digraphs(plaintext)
        out = []
        for a, b in digraphs:
            ra, ca = self.pos[a]
            rb, cb = self.pos[b]
            if ra == rb:
                out.append(self.grid[ra][(ca + 1) % 5])
                out.append(self.grid[rb][(cb + 1) % 5])
            elif ca == cb:
                out.append(self.grid[(ra + 1) % 5][ca])
                out.append(self.grid[(rb + 1) % 5][cb])
            else:
                out.append(self.grid[ra][cb])
                out.append(self.grid[rb][ca])
        return "".join(out)

    def decrypt(self, ciphertext: str) -> str:
        ciphertext = clean_text(ciphertext)
        pairs = [ciphertext[i:i + 2] for i in range(0, len(ciphertext), 2)]
        out = []
        for pair in pairs:
            a, b = pair[0], pair[1]
            ra, ca = self.pos[a]
            rb, cb = self.pos[b]
            if ra == rb:
                out.append(self.grid[ra][(ca - 1) % 5])
                out.append(self.grid[rb][(cb - 1) % 5])
            elif ca == cb:
                out.append(self.grid[(ra - 1) % 5][ca])
                out.append(self.grid[(rb - 1) % 5][cb])
            else:
                out.append(self.grid[ra][cb])
                out.append(self.grid[rb][ca])
        return "".join(out)


# ======================================================================
# 4. HILL CIPHER
# ======================================================================

class HillCipher:
    """
    Polygraphic substitution cipher: C = K . P (mod 26)
    Key matrix must be invertible mod 26, i.e. gcd(det(K), 26) == 1.
    """

    def __init__(self, key_matrix):
        self.K = key_matrix
        self.n = len(key_matrix)
        for row in key_matrix:
            if len(row) != self.n:
                raise ValueError("Key matrix must be square (n x n).")
        self.mm = MatrixMod(ALPHABET_SIZE)
        self.det = self.mm.determinant(self.K) % ALPHABET_SIZE
        if gcd(self.det, ALPHABET_SIZE) != 1:
            raise ValueError(
                f"Key matrix is not invertible mod 26 "
                f"(det={self.det}, gcd(det,26)={gcd(self.det, ALPHABET_SIZE)} != 1)."
            )
        self.K_inv = self.mm.inverse(self.K)

    def _process(self, text, matrix):
        text = clean_text(text)
        if len(text) % self.n != 0:
            text += "X" * (self.n - len(text) % self.n)  # padding
        out = []
        for i in range(0, len(text), self.n):
            block = text[i:i + self.n]
            vec = [ord(c) - ord('A') for c in block]
            new_vec = self.mm.multiply_vector(matrix, vec)
            out.extend(chr(v + ord('A')) for v in new_vec)
        return "".join(out)

    def encrypt(self, plaintext: str) -> str:
        return self._process(plaintext, self.K)

    def decrypt(self, ciphertext: str) -> str:
        return self._process(ciphertext, self.K_inv)


# ======================================================================
# CRYPTANALYSIS TOOLS
# ======================================================================

def caesar_brute_force(ciphertext: str):
    """Try all 26 possible keys and return list of (key, plaintext)."""
    results = []
    for k in range(ALPHABET_SIZE):
        candidate = CaesarCipher(k).decrypt(ciphertext)
        results.append((k, candidate))
    return results


def frequency_analysis(text: str):
    """
    Return letter frequency percentages for the given text, sorted by
    frequency descending. Useful for spotting the most likely Caesar shift
    by comparing against ENGLISH_FREQ (e.g. most common letter is likely 'E').
    """
    letters = clean_text(text)
    total = len(letters)
    if total == 0:
        return []
    counts = Counter(letters)
    freqs = [(ch, (counts.get(ch, 0) / total) * 100) for ch in
              sorted(counts, key=lambda c: -counts[c])]
    return freqs


def caesar_frequency_guess(ciphertext: str) -> int:
    """
    Guess the Caesar key using chi-squared statistic against English letter
    frequencies. Returns the most likely key.
    """
    best_key, best_score = 0, float("inf")
    for k in range(ALPHABET_SIZE):
        candidate = CaesarCipher(k).decrypt(ciphertext)
        letters = clean_text(candidate)
        if not letters:
            continue
        counts = Counter(letters)
        total = len(letters)
        chi_sq = 0.0
        for ch in "ABCDEFGHIJKLMNOPQRSTUVWXYZ":
            observed = counts.get(ch, 0)
            expected = ENGLISH_FREQ[ch] / 100 * total
            if expected > 0:
                chi_sq += ((observed - expected) ** 2) / expected
        if chi_sq < best_score:
            best_score, best_key = chi_sq, k
    return best_key


def hill_known_plaintext_attack(plaintext_blocks, ciphertext_blocks, n):
    """
    Recover the Hill cipher key matrix K given n known plaintext/ciphertext
    block pairs (each block is a string of length n), assuming the plaintext
    block matrix is invertible mod 26.

    K satisfies: C = K . P (mod 26)  =>  K = C . P^-1 (mod 26)

    plaintext_blocks / ciphertext_blocks: list of n strings, each length n.
    Returns the recovered key matrix K (n x n).
    """
    if len(plaintext_blocks) != n or len(ciphertext_blocks) != n:
        raise ValueError(f"Need exactly {n} plaintext/ciphertext blocks "
                          f"of length {n} to solve for an {n}x{n} key.")

    mm = MatrixMod(ALPHABET_SIZE)

    # Build P and C as matrices where each COLUMN is one block's vector
    P = [[ord(blk[row]) - ord('A') for blk in plaintext_blocks]
         for row in range(n)]
    C = [[ord(blk[row]) - ord('A') for blk in ciphertext_blocks]
         for row in range(n)]

    P_inv = mm.inverse(P)
    K = mm.multiply(C, P_inv)
    return K


# ======================================================================
# COMPARISON SUMMARY
# ======================================================================

def print_comparison_table():
    rows = [
        ("Caesar", "26", "Very Low",
         "Trivial (brute force / frequency analysis)"),
        ("Vigenere", "26^L (L=key length)", "Low-Medium",
         "Vulnerable via Kasiski examination / Index of Coincidence"),
        ("Playfair", "~25! (grid arrangements)", "Medium",
         "Vulnerable to digraph frequency analysis"),
        ("Hill (2x2)", "~157 invertible matrices mod 26", "Medium",
         "Fully broken by known-plaintext attack (linear algebra)"),
    ]
    print(f"{'Cipher':<10} {'Key Space':<32} {'Security':<12} {'Main Weakness'}")
    print("-" * 100)
    for r in rows:
        print(f"{r[0]:<10} {r[1]:<32} {r[2]:<12} {r[3]}")


# ======================================================================
# AUTOMATED TEST SUITE
# ======================================================================

import unittest


class TestCaesarCipher(unittest.TestCase):
    def test_encrypt_known_vector(self):
        self.assertEqual(CaesarCipher(3).encrypt("HELLO"), "KHOOR")

    def test_decrypt_known_vector(self):
        self.assertEqual(CaesarCipher(3).decrypt("KHOOR"), "HELLO")

    def test_wraparound(self):
        self.assertEqual(CaesarCipher(3).encrypt("XYZ"), "ABC")

    def test_non_alpha_passthrough(self):
        c = CaesarCipher(5)
        enc = c.encrypt("Hello, World! 123")
        self.assertEqual(c.decrypt(enc), "Hello, World! 123")

    def test_case_preservation(self):
        self.assertEqual(CaesarCipher(1).encrypt("aBc"), "bCd")


class TestVigenereCipher(unittest.TestCase):
    def test_encrypt_known_vector(self):
        # Classic example: key "LEMON", plaintext "ATTACKATDAWN" -> "LXFOPVEFRNHR"
        v = VigenereCipher("LEMON")
        self.assertEqual(v.encrypt("ATTACKATDAWN"), "LXFOPVEFRNHR")

    def test_decrypt_known_vector(self):
        v = VigenereCipher("LEMON")
        self.assertEqual(v.decrypt("LXFOPVEFRNHR"), "ATTACKATDAWN")

    def test_round_trip_mixed_text(self):
        v = VigenereCipher("KEY")
        pt = "Meet Me At Noon!"
        self.assertEqual(v.decrypt(v.encrypt(pt)), pt)


class TestPlayfairCipher(unittest.TestCase):
    def test_grid_construction(self):
        cipher = PlayfairCipher("MONARCHY")
        expected = [
            ['M', 'O', 'N', 'A', 'R'],
            ['C', 'H', 'Y', 'B', 'D'],
            ['E', 'F', 'G', 'I', 'K'],
            ['L', 'P', 'Q', 'S', 'T'],
            ['U', 'V', 'W', 'X', 'Z'],
        ]
        self.assertEqual(cipher.grid, expected)

    def test_encrypt_known_vector(self):
        cipher = PlayfairCipher("MONARCHY")
        self.assertEqual(cipher.encrypt("HELLO"), "CFSUPM")

    def test_decrypt_known_vector(self):
        cipher = PlayfairCipher("MONARCHY")
        self.assertEqual(cipher.decrypt("CFSUPM"), "HELXLO")

    def test_double_letter_padding(self):
        cipher = PlayfairCipher("KEYWORD")
        digraphs = cipher._prepare_digraphs("BALLOON")
        self.assertIn(("L", "X"), digraphs)

    def test_odd_length_padding(self):
        cipher = PlayfairCipher("KEYWORD")
        digraphs = cipher._prepare_digraphs("ABC")
        self.assertEqual(digraphs[-1], ("C", "X"))

    def test_round_trip(self):
        cipher = PlayfairCipher("SECRETKEY")
        plaintext = "ATTACKATDAWN"
        enc = cipher.encrypt(plaintext)
        dec = cipher.decrypt(enc)
        self.assertEqual(dec.replace("X", ""), plaintext.replace("X", ""))


class TestHillCipher(unittest.TestCase):
    def test_invertibility_check_rejects_bad_key(self):
        with self.assertRaises(ValueError):
            HillCipher([[2, 4], [4, 8]])  # det = 0, not invertible

    def test_encrypt_known_vector(self):
        cipher = HillCipher([[3, 3], [2, 5]])
        self.assertEqual(cipher.encrypt("HI"), "TC")

    def test_decrypt_known_vector(self):
        cipher = HillCipher([[3, 3], [2, 5]])
        self.assertEqual(cipher.decrypt("TC"), "HI")

    def test_round_trip_with_padding(self):
        cipher = HillCipher([[3, 3], [2, 5]])
        plaintext = "ATTACK"
        self.assertEqual(cipher.decrypt(cipher.encrypt(plaintext)), plaintext)

    def test_odd_length_padding(self):
        cipher = HillCipher([[3, 3], [2, 5]])
        encrypted = cipher.encrypt("CAT")
        self.assertEqual(len(encrypted) % 2, 0)

    def test_3x3_matrix(self):
        K = [[6, 24, 1], [13, 16, 10], [20, 17, 15]]
        cipher = HillCipher(K)
        self.assertEqual(cipher.encrypt("ACT"), "POH")
        self.assertEqual(cipher.decrypt("POH"), "ACT")


class TestCryptanalysis(unittest.TestCase):
    def test_caesar_brute_force_finds_plaintext(self):
        ct = CaesarCipher(7).encrypt("ATTACKATDAWN")
        results = caesar_brute_force(ct)
        plaintexts = [pt for _, pt in results]
        self.assertIn("ATTACKATDAWN", plaintexts)

    def test_caesar_frequency_guess(self):
        # Longer text gives frequency analysis enough signal to work with
        plaintext = ("THEQUICKBROWNFOXJUMPSOVERTHELAZYDOG" * 5)
        ct = CaesarCipher(11).encrypt(plaintext)
        guessed_key = caesar_frequency_guess(ct)
        self.assertEqual(guessed_key, 11)

    def test_hill_known_plaintext_attack_recovers_key(self):
        true_K = [[3, 3], [2, 5]]
        cipher = HillCipher(true_K)
        plaintext_blocks = ["HI", "AT"]
        ciphertext_blocks = [cipher.encrypt(b) for b in plaintext_blocks]
        recovered_K = hill_known_plaintext_attack(
            plaintext_blocks, ciphertext_blocks, n=2)
        self.assertEqual(recovered_K, true_K)


# ======================================================================
# INTERACTIVE CLI
# ======================================================================

def _prompt(msg):
    return input(msg).strip()


def cli_caesar():
    key = int(_prompt("Enter key (integer): "))
    cipher = CaesarCipher(key)
    mode = _prompt("Encrypt or Decrypt? [e/d]: ").lower()
    text = _prompt("Enter text: ")
    print("Result:", cipher.encrypt(text) if mode == "e" else cipher.decrypt(text))


def cli_vigenere():
    key = _prompt("Enter key (letters only): ")
    cipher = VigenereCipher(key)
    mode = _prompt("Encrypt or Decrypt? [e/d]: ").lower()
    text = _prompt("Enter text: ")
    print("Result:", cipher.encrypt(text) if mode == "e" else cipher.decrypt(text))


def cli_playfair():
    key = _prompt("Enter key phrase: ")
    cipher = PlayfairCipher(key)
    mode = _prompt("Encrypt or Decrypt? [e/d]: ").lower()
    text = _prompt("Enter text: ")
    print("Grid:")
    for row in cipher.grid:
        print(" ".join(row))
    print("Result:", cipher.encrypt(text) if mode == "e" else cipher.decrypt(text))


def cli_hill():
    n = int(_prompt("Matrix size n (e.g. 2 or 3): "))
    print(f"Enter the {n}x{n} key matrix, row by row, space-separated:")
    matrix = []
    for i in range(n):
        row = [int(x) for x in _prompt(f"Row {i + 1}: ").split()]
        if len(row) != n:
            print("Invalid row length. Aborting.")
            return
        matrix.append(row)
    try:
        cipher = HillCipher(matrix)
    except ValueError as e:
        print("Error:", e)
        return
    mode = _prompt("Encrypt or Decrypt? [e/d]: ").lower()
    text = _prompt("Enter text: ")
    print("Result:", cipher.encrypt(text) if mode == "e" else cipher.decrypt(text))


def cli_cryptanalysis():
    print("1. Caesar brute force")
    print("2. Caesar frequency-based guess")
    print("3. Frequency analysis of text")
    print("4. Hill known-plaintext attack (2x2)")
    choice = _prompt("Choose an option: ")
    if choice == "1":
        ct = _prompt("Enter ciphertext: ")
        for k, pt in caesar_brute_force(ct):
            print(f"  key={k:2d}: {pt}")
    elif choice == "2":
        ct = _prompt("Enter ciphertext: ")
        key = caesar_frequency_guess(ct)
        print(f"Most likely key: {key}")
        print(f"Decrypted text : {CaesarCipher(key).decrypt(ct)}")
    elif choice == "3":
        text = _prompt("Enter text: ")
        for ch, pct in frequency_analysis(text):
            print(f"  {ch}: {pct:.2f}%")
    elif choice == "4":
        p1 = _prompt("Known plaintext block 1 (len 2): ").upper()
        c1 = _prompt("Corresponding ciphertext block 1 (len 2): ").upper()
        p2 = _prompt("Known plaintext block 2 (len 2): ").upper()
        c2 = _prompt("Corresponding ciphertext block 2 (len 2): ").upper()
        try:
            K = hill_known_plaintext_attack([p1, p2], [c1, c2], n=2)
            print("Recovered key matrix:", K)
        except ValueError as e:
            print("Error:", e)
    else:
        print("Invalid option.")


def main_menu():
    while True:
        print("\n" + "=" * 50)
        print("CLASSICAL CIPHERS TOOLKIT")
        print("=" * 50)
        print("1. Caesar Cipher")
        print("2. Vigenere Cipher")
        print("3. Playfair Cipher")
        print("4. Hill Cipher")
        print("5. Cryptanalysis Tools")
        print("6. Comparison Summary")
        print("7. Run Automated Tests")
        print("0. Exit")
        choice = _prompt("Select an option: ")
        try:
            if choice == "1":
                cli_caesar()
            elif choice == "2":
                cli_vigenere()
            elif choice == "3":
                cli_playfair()
            elif choice == "4":
                cli_hill()
            elif choice == "5":
                cli_cryptanalysis()
            elif choice == "6":
                print_comparison_table()
            elif choice == "7":
                unittest.main(argv=[""], exit=False, verbosity=2)
            elif choice == "0":
                print("Goodbye.")
                break
            else:
                print("Invalid option, try again.")
        except Exception as e:
            print("Error:", e)


# ======================================================================
# ENTRY POINT
# ======================================================================

if __name__ == "__main__":
    if "--test" in sys.argv:
        unittest.main(argv=[""], exit=False, verbosity=2)
    else:
        main_menu()
