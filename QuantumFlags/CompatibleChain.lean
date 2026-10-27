import QuantumFlags.FiniteBases

/-!
A conditional passage from a quantum division-ring chain to the global flags.
This structure lists properties of the chain, not the desired flags (B) or (F).
Construction of an inhabitant from Ore localizations is a separate obligation.
-/

namespace QuantumFlags

variable {D : Type*} [DivisionRing D] [CharZero D]

structure QuantumChain (D : Type*) [DivisionRing D] [CharZero D] where
  x : ℕ → D
  layer : ℕ → Subfield D
  increasing : Monotone layer
  covers : ∀ a : D, ∃ n, a ∈ layer n
  generator_mem : ∀ k, x k ∈ layer (k+1)
  not_rational : ∀ k, NotRational (x k)
  adjacent : ∀ n, x (n+1)*x n = half D*x n*x (n+1)
  distant : ∀ i j, i+1 < j → Commute (x i) (x j)
  remote : ∀ n a, a ∈ layer n → Commute a (x (n+1))
  normalizer : ∀ n, layer n ≃+* layer n
  normalizes : ∀ n (a : layer n), x n*(a : D) = (normalizer n a : D)*x n
  right_pair_independent : ∀ n, Function.Injective (rightEval (layer n).subtype (x n))
  left_pair_independent : ∀ n, Function.Injective (leftEval (layer n).subtype (x n))

def innerHom (g : D) (hg : g ≠ 0) : D →+* D where
  toFun a := g*a*g⁻¹
  map_zero' := by simp
  map_one' := by simp [hg]
  map_add' a b := by noncomm_ring
  map_mul' a b := by simp only [mul_assoc, inv_mul_cancel_left₀ hg]

def localConj (Q : QuantumChain D) (p n : ℕ) : D →+* D :=
  innerHom (gamma Q.x p n) (gamma_ne_zero Q.x Q.not_rational p n)

theorem localConj_succ (Q : QuantumChain D) (p n : ℕ) (a : D) (ha : a ∈ Q.layer n) :
    localConj Q p (n+1) a = localConj Q p n a := by
  have hc : Commute a (poch (half D) p (Q.x (n+1))) :=
    commute_poch _ _ _ (Rat.cast_commute _ a).symm (Q.remote n a ha) p
  have hn : poch (half D) p (Q.x (n+1)) ≠ 0 :=
    poch_ne_zero _ (Q.not_rational (n+1)) (1/2) p
  change (gamma Q.x p n * poch (half D) p (Q.x (n+1)))*a*
      (gamma Q.x p n * poch (half D) p (Q.x (n+1)))⁻¹ = _
  rw [mul_inv_rev]
  simp only [localConj, innerHom, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
  calc
    _ = gamma Q.x p n * (poch (half D) p (Q.x (n+1))*a*
        (poch (half D) p (Q.x (n+1)))⁻¹) * (gamma Q.x p n)⁻¹ := by simp [mul_assoc]
    _ = _ := by rw [← hc.eq, mul_assoc a, mul_inv_cancel₀ hn, mul_one]

theorem localConj_compatible (Q : QuantumChain D) (p n m : ℕ) (hnm : n ≤ m)
    (a : D) (ha : a ∈ Q.layer n) : localConj Q p m a = localConj Q p n a := by
  induction m, hnm using Nat.le_induction with
  | base => rfl
  | succ m h ih =>
    rw [localConj_succ Q p m a (Q.increasing h ha), ih]

noncomputable def kappaFn (Q : QuantumChain D) (p : ℕ) (a : D) : D := by
  classical
  exact localConj Q p (Nat.find (Q.covers a)) a

theorem kappaFn_at (Q : QuantumChain D) (p n : ℕ) (a : D) (ha : a ∈ Q.layer n) :
    kappaFn Q p a = localConj Q p n a := by
  classical
  let k := Nat.find (Q.covers a)
  have hk : a ∈ Q.layer k := Nat.find_spec (Q.covers a)
  exact (localConj_compatible Q p k (max k n) (le_max_left _ _) a hk).symm.trans
    (localConj_compatible Q p n (max k n) (le_max_right _ _) a ha)

theorem common_layer (Q : QuantumChain D) (a b : D) :
    ∃ n, a ∈ Q.layer n ∧ b ∈ Q.layer n := by
  obtain ⟨n, hn⟩ := Q.covers a
  obtain ⟨m, hm⟩ := Q.covers b
  exact ⟨max n m, Q.increasing (le_max_left _ _) hn,
    Q.increasing (le_max_right _ _) hm⟩

noncomputable def kappa (Q : QuantumChain D) (p : ℕ) : D →+* D where
  toFun := kappaFn Q p
  map_zero' := by rw [kappaFn_at Q p 0 0 (Q.layer 0).zero_mem]; exact map_zero _
  map_one' := by rw [kappaFn_at Q p 0 1 (Q.layer 0).one_mem]; exact map_one _
  map_add' a b := by
    obtain ⟨n, ha, hb⟩ := common_layer Q a b
    rw [kappaFn_at Q p n _ ((Q.layer n).add_mem ha hb),
      kappaFn_at Q p n a ha, kappaFn_at Q p n b hb]
    exact map_add _ a b
  map_mul' a b := by
    obtain ⟨n, ha, hb⟩ := common_layer Q a b
    rw [kappaFn_at Q p n _ ((Q.layer n).mul_mem ha hb),
      kappaFn_at Q p n a ha, kappaFn_at Q p n b hb]
    exact map_mul _ a b

theorem kappa_at (Q : QuantumChain D) (p n : ℕ) (a : D) (ha : a ∈ Q.layer n) :
    kappa Q p a = gamma Q.x p n * a * (gamma Q.x p n)⁻¹ :=
  kappaFn_at Q p n a ha

def localGenerators (Q : QuantumChain D) (n k : ℕ) : Q.layer n :=
  if h : k < n then
    ⟨Q.x k, Q.increasing (Nat.succ_le_of_lt h) (Q.generator_mem k)⟩
  else 1

theorem localGenerators_nonzero (Q : QuantumChain D) (n k : ℕ) :
    localGenerators Q n k ≠ 0 := by
  unfold localGenerators
  split_ifs with h
  · intro he
    have he' := congrArg (fun a : Q.layer n => (a : D)) he
    exact notRational_ne_zero (Q.not_rational k) he'
  · exact one_ne_zero

theorem localGenerators_prefix (Q : QuantumChain D) (n k : ℕ) (h : k < n) :
    (localGenerators Q n k : D) = Q.x k := by simp [localGenerators, h]

theorem chain_finite_adjacent_flags (Q : QuantumChain D) (p n : ℕ) (hp : 1 ≤ p) :
    Function.Injective (leftConjugatedStrip (Q.layer n).subtype (Q.x 0) (gamma Q.x p n)) ∧
    Function.Injective
      (rightConjugatedStrip (Q.layer n).subtype (Q.x 0) (gamma Q.x (p+1) n)) ∧
    Set.range (leftConjugatedStrip (Q.layer n).subtype (Q.x 0) (gamma Q.x p n)) =
      Set.range (rightConjugatedStrip (Q.layer n).subtype (Q.x 0) (gamma Q.x (p+1) n)) := by
  exact finite_adjacent_flags _ Q.x Q.not_rational Q.adjacent Q.distant p n hp
    (localGenerators Q n) (localGenerators_nonzero Q n) (localGenerators_prefix Q n)
    (Q.right_pair_independent n) (Q.left_pair_independent n) (Q.normalizer n)
    (Q.normalizes n)

end QuantumFlags
