import QuantumFlags.RightArtinian

namespace QuantumFlags

noncomputable section

variable {A : Type*} {B : Type*} [Ring A] [Ring B]

/-- The fixed part of the idempotent image of 1 under a nonunital ring map. -/
def cornerFixedGroup (f : A →ₙ+* B) (M : Type*) [AddCommGroup M] [Module B M] :
    AddSubgroup M where
  carrier := {x | f 1 • x = x}
  zero_mem' := by simp
  add_mem' {x y} hx hy := by
    change f 1 • (x+y) = x+y
    change f 1 • x = x at hx
    change f 1 • y = y at hy
    rw [smul_add,hx,hy]
  neg_mem' {x} hx := by
    change f 1 • (-x) = -x
    change f 1 • x = x at hx
    rw [smul_neg,hx]

@[instance_reducible]
def cornerFixedModule (f : A →ₙ+* B) (M : Type*) [AddCommGroup M] [Module B M] :
    Module A (cornerFixedGroup f M) where
  smul a x := ⟨f a • (x : M), by
    change f 1 • (f a • (x : M)) = f a • (x : M)
    rw [← mul_smul,← map_mul,one_mul]⟩
  one_smul x := Subtype.ext x.property
  mul_smul a b x := by
    apply Subtype.ext
    change f (a*b) • (x : M) = f a • (f b • (x : M))
    rw [map_mul,mul_smul]
  zero_smul x := by
    apply Subtype.ext
    change f 0 • (x : M) = 0
    rw [map_zero,zero_smul]
  smul_zero a := by
    apply Subtype.ext
    exact smul_zero (f a)
  smul_add a x y := by
    apply Subtype.ext
    exact smul_add (f a) (x : M) (y : M)
  add_smul a b x := by
    apply Subtype.ext
    change f (a+b) • (x : M) = f a • (x : M)+f b • (x : M)
    rw [map_add,add_smul]

theorem cornerFixed_smul (f : A →ₙ+* B) (M : Type*) [AddCommGroup M] [Module B M]
    (a : A) (x : cornerFixedGroup f M) :
    letI := cornerFixedModule f M
    ((a • x : cornerFixedGroup f M) : M) = f a • (x : M) := rfl

theorem corner_projection_idempotent (f : A →ₙ+* B) (M : Type*) [AddCommGroup M] [Module B M]
    (x : M) : f 1 • (f 1 • x) = f 1 • x := by
  rw [← mul_smul,← map_mul,one_mul]

def cornerFixedMap (f : A →ₙ+* B) {M : Type*} {P : Type*} [AddCommGroup M] [Module B M]
    [AddCommGroup P] [Module B P] (g : M →ₗ[B] P) :
    letI := cornerFixedModule f M
    letI := cornerFixedModule f P
    cornerFixedGroup f M →ₗ[A] cornerFixedGroup f P := by
  letI := cornerFixedModule f M
  letI := cornerFixedModule f P
  exact {
    toFun x := ⟨g x, by
      change f 1 • g (x : M) = g (x : M)
      rw [← g.map_smul,x.property]⟩
    map_add' x y := Subtype.ext (g.map_add (x : M) (y : M))
    map_smul' a x := Subtype.ext (g.map_smul (f a) (x : M)) }

theorem cornerFixedMap_apply (f : A →ₙ+* B) {M : Type*} {P : Type*} [AddCommGroup M] [Module B M]
    [AddCommGroup P] [Module B P] (g : M →ₗ[B] P) (x : cornerFixedGroup f M) :
    (cornerFixedMap f g x : P) = g (x : M) := rfl

theorem cornerFixedMap_surjective (f : A →ₙ+* B) {M : Type*} {P : Type*} [AddCommGroup M] [Module B M]
    [AddCommGroup P] [Module B P] (g : M →ₗ[B] P) (hg : Function.Surjective g) :
    Function.Surjective (cornerFixedMap f g) := by
  rintro ⟨z,hz⟩
  obtain ⟨x,hx⟩ := hg z
  refine ⟨⟨f 1 • x,corner_projection_idempotent f M x⟩, ?_⟩
  apply Subtype.ext
  change g (f 1 • x) = z
  rw [g.map_smul,hx]
  exact hz

def cornerFixedPiEquiv (f : A →ₙ+* B) (I : Type*) (M : Type*) [AddCommGroup M] [Module B M] :
    letI := cornerFixedModule f M
    letI := cornerFixedModule f (I → M)
    cornerFixedGroup f (I → M) ≃ₗ[A] (I → cornerFixedGroup f M) := by
  letI := cornerFixedModule f M
  letI := cornerFixedModule f (I → M)
  exact {
    toFun x i := ⟨(x : I → M) i,congrFun x.property i⟩
    invFun x := ⟨fun i => (x i : M), by funext i; exact (x i).property⟩
    left_inv x := by apply Subtype.ext; rfl
    right_inv x := by funext i; apply Subtype.ext; rfl
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }

end

end QuantumFlags
