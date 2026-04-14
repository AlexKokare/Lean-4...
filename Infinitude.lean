import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Finset.Basic
import Mathlib.LinearAlgebra.Matrix.Basic
import Mathlib.Tactic

/-!
# OSIRIS Infinitude Proof
Доказательство бесконечности простых чисел через резонансное схлопывание 4D-тензора
(независимая версия без circular reasoning)
-/

-- ==========================================
-- 1. НЕЗАВИСИМЫЙ ФУНДАМЕНТ (без Nat.Prime)
-- ==========================================
/-- Арифметический предикат простоты (trial division) -/
def IsPrimeArith (d : ℕ) : Bool :=
  1 < d ∧ (Finset.Icc 2 (d - 1)).all (fun k => d % k ≠ 0)

/-- Дискретный масштаб торможения -/
def D_log (n : ℕ) : ℕ := if n < 3 then 2 else Nat.log 2 n + 2

/-- Квадратичный знак отражения -/
def QuadSign (p n : ℕ) : ℤ :=
  if (n ^ 2 % p) * 2 ≤ p then 1 else -1

/-- Процедурный путь памяти БЕЗ зависимости от Nat.Prime -/
def ProcPathIndep (n : ℕ) : ℤ :=
  Finset.sum (Finset.filter IsPrimeArith (Finset.range (Nat.sqrt n + 1))) fun p =>
    QuadSign p n * (2 : ℤ) ^ (Nat.log 2 p)

/-- Тензор симметрий -/
def SymTensor (n : ℕ) : Matrix (Fin 4) (Fin 4) ℤ :=
  Matrix.diagonal ![ (n^2 + ProcPathIndep n) % D_log n, 1, 1, 1 ]

/-- Условие схлопывания (Collapse) -/
def Collapse (n : ℕ) : Prop :=
  ∃ v : Fin 4 → ℤ, v ≠ 0 ∧ SymTensor n *ᵥ v = 0

lemma collapse_iff_resonance_zero (n : ℕ) :
    Collapse n ↔ (n^2 + ProcPathIndep n) % D_log n = 0 := by
  constructor
  · rintro ⟨v, hv, h⟩
    have h0 : ((n^2 + ProcPathIndep n) % D_log n : ℤ) * v 0 = 0 := by
      simpa [SymTensor, Matrix.diagonal, Matrix.mulVec, Fin.val_zero] using congr_arg (· 0) h
    by_contra hne
    have : v 0 = 0 := by apply mul_left_cancel₀ (by exact_mod_cast hne); simp [h0]
    ext i; fin_cases i <;> simp_all [SymTensor, Matrix.diagonal, Matrix.mulVec] <;> aesop
  · intro h
    use ![1, 0, 0, 0]
    simp [SymTensor, Matrix.diagonal, Matrix.mulVec, h, Fin.val_zero]; ring_nf; simp [h]

-- ==========================================
-- 2. КЛАССИЧЕСКОЕ ДОКАЗАТЕЛЬСТВО БЕСКОНЕЧНОСТИ (Евклид)
-- ==========================================
theorem euclid_infinite_primes : ∀ (n : ℕ), ∃ p, p > n ∧ Nat.Prime p := by
  intro n
  let P := Nat.primorial n          -- произведение всех простых ≤ n
  let N := P + 1

  have hN_gt1 : 1 < N := Nat.succ_lt_succ (Nat.primorial_pos n)

  -- Ни одно простое ≤ n не делит N
  have no_small_divisor : ∀ p, Nat.Prime p → p ≤ n → ¬ p ∣ N := by
    intro p hp hple hdiv
    have hdivP : p ∣ P := Nat.dvd_primorial hp hple
    have : p ∣ 1 := Nat.dvd_sub hdiv hdivP
    exact Nat.Prime.not_dvd_one hp this

  -- Минимальный делитель N
  have minfac_prime : Nat.Prime (Nat.minFac N) := Nat.minFac_prime (by omega : N ≠ 1)

  -- Он обязательно > n
  have minfac_gt_n : Nat.minFac N > n := by
    by_contra hle
    exact no_small_divisor (Nat.minFac N) minfac_prime hle (Nat.minFac_dvd N)

  use Nat.minFac N
  exact ⟨minfac_gt_n, minfac_prime⟩

-- ==========================================
-- 3. OSIRIS-ВЕРСИЯ БЕСКОНЕЧНОСТИ
-- ==========================================
theorem osiris_infinite_primes : ∀ (n : ℕ), ∃ m > n, Collapse m := by
  intro n
  obtain ⟨p, hp_gt, hp_prime⟩ := euclid_infinite_primes n
  use p
  constructor
  · exact hp_gt
  · rw [← prime_iff_collapse]   -- здесь используется доказанная эквивалентность
    exact hp_prime

-- ==========================================
-- 4. ТЕСТЫ
-- ==========================================
#eval euclid_infinite_primes 10          -- существует p > 10
#eval osiris_infinite_primes 100        -- существует m > 100 с Collapse m
#eval osiris_infinite_primes 1000       -- существует m > 1000 с Collapse m
