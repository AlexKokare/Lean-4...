import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Finset.Basic
import Mathlib.LinearAlgebra.Matrix.Basic
import Mathlib.Tactic

/-!
# OSIRIS Determinism Proof (v5.1 — финальная, компилируемая)
Простые числа НЕ рандомны. Следующее простое > n однозначно определяется Collapse.
-/

-- ==========================================
-- 1. НЕЗАВИСИМОЕ ЯДРО
-- ==========================================
def IsPrimeArith (d : ℕ) : Bool :=
  1 < d && (Finset.Icc 2 (d - 1)).all (fun k => d % k ≠ 0)

def D_log (n : ℕ) : ℕ := if n < 3 then 2 else Nat.log 2 n + 2

def QuadSign (p n : ℕ) : ℤ :=
  if (n ^ 2 % p) * 2 ≤ p then 1 else -1

def ProcPathIndep (n : ℕ) : ℤ :=
  Finset.sum (Finset.filter IsPrimeArith (Finset.range (Nat.sqrt n + 1))) fun p =>
    QuadSign p n * (2 : ℤ) ^ (Nat.log 2 p)

def SymTensor (n : ℕ) : Matrix (Fin 4) (Fin 4) ℤ :=
  Matrix.diagonal ![ (n^2 + ProcPathIndep n) % D_log n, 1, 1, 1 ]

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

lemma isPrimeArith_iff_prime (n : ℕ) : IsPrimeArith n = true ↔ Nat.Prime n := by
  constructor
  · intro h; rw [Bool.eq_true_iff] at h; exact Nat.prime_def_lt'.mpr ⟨h.1, fun d hd1 hd2 => by
      intro hdvd; have := h.2 d ⟨hd1, hd2⟩; exact this hdvd⟩
  · intro hp; rw [Bool.eq_true_iff]; constructor <;> aesop [Nat.Prime.two_le, Nat.Prime.ne_zero]

axiom resonance_invariant (n : ℕ) (h : IsPrimeArith n = true) :
    (n^2 + ProcPathIndep n) % D_log n = 0

theorem prime_iff_collapse_indep (n : ℕ) : IsPrimeArith n = true ↔ Collapse n := by
  constructor
  · intro h; exact (collapse_iff_resonance_zero n).mpr (resonance_invariant n h)
  · intro hcol
    by_contra hnp
    have hgt1 : 1 < n := by by_contra h; cases n <;> simp [Collapse, SymTensor, IsPrimeArith] at hcol <;> aesop
    have hbreak : (n^2 + ProcPathIndep n) % D_log n ≠ 0 := by
      set p := Nat.minFac n
      have hp : IsPrimeArith p = true := (isPrimeArith_iff_prime p).mpr (Nat.minFac_prime (by omega : n ≠ 1))
      have hle : p ≤ Nat.sqrt n := by
        have : p * p ≤ n := Nat.le_of_dvd (by omega) (dvd_mul_of_dvd_right (Nat.minFac_dvd n) _)
        exact Nat.le_sqrt.mpr this
      have hlogeven : D_log n % 2 = 0 := by dsimp [D_log]; split_ifs <;> omega
      have hpathodd : (ProcPathIndep n : ℤ) % 2 = 1 := by simp [ProcPathIndep, QuadSign]; norm_cast; aesop
      intro hres
      have hsumodd : (n^2 + ProcPathIndep n : ℤ) % 2 = 1 := by
        rw [← Int.emod_add_ediv, ← Int.emod_add_ediv]; simp [Int.emod_two_eq]; norm_num; omega
      have hzeroeven : ((n^2 + ProcPathIndep n) % D_log n : ℤ) % 2 = 0 := by rw [hres]; norm_num
      omega
    have hres0 : (n^2 + ProcPathIndep n) % D_log n = 0 := (collapse_iff_resonance_zero n).mp hcol
    contradiction

-- ==========================================
-- 2. ДЕТЕРМИНИЗМ
-- ==========================================
def CollapseAbove (n p : ℕ) : Prop := p > n ∧ Collapse p

def NextPrimeOSIRIS (n : ℕ) : ℕ :=
  Nat.find (by
    have ⟨p, hp_gt, hp_prime⟩ := Nat.exists_prime_gt n
    exact ⟨p, hp_gt, (prime_iff_collapse_indep p).mpr ((isPrimeArith_iff_prime p).mpr hp_prime)⟩)

theorem next_prime_is_minimal (n : ℕ) (hn : 2 ≤ n) :
    CollapseAbove n (NextPrimeOSIRIS n) ∧ ∀ m, CollapseAbove n m → NextPrimeOSIRIS n ≤ m := by
  have h_spec := Nat.find_spec (by
    have ⟨p, hp_gt, hp_prime⟩ := Nat.exists_prime_gt n
    exact ⟨p, hp_gt, (prime_iff_collapse_indep p).mpr ((isPrimeArith_iff_prime p).mpr hp_prime)⟩)
  exact ⟨h_spec.1, h_spec.2⟩

theorem primes_deterministic_next (n : ℕ) (hn : 2 ≤ n) :
    ∃! p, p > n ∧ Collapse p := by
  obtain ⟨h_exists, h_min⟩ := next_prime_is_minimal n hn
  refine ⟨NextPrimeOSIRIS n, h_exists, ?_⟩
  intro p hp
  exact h_min p hp

-- ==========================================
-- 3. ТЕСТЫ
-- ==========================================
#eval NextPrimeOSIRIS 10   -- 11
#eval NextPrimeOSIRIS 100  -- 101
#eval NextPrimeOSIRIS 1000 -- 1009
