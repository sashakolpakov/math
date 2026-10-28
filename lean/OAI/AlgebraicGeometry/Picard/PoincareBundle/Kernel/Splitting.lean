import OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme
import OAI.AlgebraicGeometry.Picard.PoincareBundle.CoprimeKernels

/-! # Splitting -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Splitting

noncomputable section

/-!
# Coprime splitting of scheme-theoretic kernels for PoincareBundle

The splitting is constructed in a cartesian category from the represented
kernel functors. Thus it applies to finite group schemes without discarding
infinitesimal test points.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u v

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
  [BraidedCategory C]
  {A B : C} [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B]

/-- Powers of commutative group-object morphisms are group morphisms. -/
instance power_isMonHom (f : A ⟶ B) [IsMonHom f] (n : ℕ) : IsMonHom (f ^ n) := by
  induction n with
  | zero =>
      change IsMonHom (toUnit A ≫ η[B])
      infer_instance
  | succ n ih =>
      have : IsMonHom (f ^ n) := ih
      rw [pow_succ, Hom.mul_def]
      infer_instance

variable (f : A ⟶ B) [IsMonHom f] (n : ℕ)

omit [IsCommMonObj A] in
theorem pointsMap_pow (T : C) :
    Scheme.pointsMap (f ^ n) T = (Scheme.pointsMap f T) ^ n := by
  ext x
  change x ≫ f ^ n = (x ≫ f) ^ n
  rw [MonObj.comp_pow]

theorem pointsMap_id_pow (T : C) :
    Scheme.pointsMap ((𝟙 A) ^ n) T = (powMonoidHom n : (T ⟶ A) →* (T ⟶ A)) := by
  ext x
  change x ≫ (𝟙 A) ^ n = x ^ n
  rw [MonObj.comp_pow, Category.comp_id]

variable [HasPullbacks C]

/-- The represented kernel of n times f has exactly the expected test points. -/
def powerKernelPointsEquiv (T : C) :
    (T ⟶ Scheme.kernelObject (f ^ n)) ≃
      ((Scheme.pointsMap f T) ^ n).ker :=
  (Scheme.kernelPointsEquiv (f ^ n) T).trans
    (MulEquiv.subgroupCongr (congrArg MonoidHom.ker (pointsMap_pow f n T))).toEquiv

/-- The represented n-torsion subgroup has all n-torsion test points. -/
def torsionKernelPointsEquiv (T : C) :
    (T ⟶ Scheme.kernelObject ((𝟙 A) ^ n)) ≃
      (powMonoidHom n : (T ⟶ A) →* (T ⟶ A)).ker :=
  (Scheme.kernelPointsEquiv ((𝟙 A) ^ n) T).trans
    (MulEquiv.subgroupCongr (congrArg MonoidHom.ker (pointsMap_id_pow (A := A) n T))).toEquiv

variable (m : ℕ) (hnm : n.Coprime m)
  (hker : ∀ (T : C) (x : T ⟶ A), x ≫ f = 1 → x ^ m = 1)

/-- The splitting equivalence on every test object. -/
def splitPointsEquiv (T : C) :
    (T ⟶ Scheme.kernelObject ((𝟙 A) ^ n) ⊗ Scheme.kernelObject f) ≃
      (T ⟶ Scheme.kernelObject (f ^ n)) :=
  homEquivToProd.trans
    ((torsionKernelPointsEquiv (A := A) n T).prodCongr
      (Scheme.kernelPointsEquiv f T)) |>.trans
    (CoprimeKernels.kernelProductEquiv (Scheme.pointsMap f T) n m hnm
      (hker T)).toEquiv |>.trans (powerKernelPointsEquiv f n T).symm

/-- The splitting adds the two kernel inclusions. -/
theorem splitPointsEquiv_comp_inclusion (T : C)
    (x : T ⟶ Scheme.kernelObject ((𝟙 A) ^ n) ⊗ Scheme.kernelObject f) :
    splitPointsEquiv f n m hnm hker T x ≫ Scheme.kernelInclusion (f ^ n) =
      (x ≫ fst _ _ ≫ Scheme.kernelInclusion ((𝟙 A) ^ n)) *
        (x ≫ snd _ _ ≫ Scheme.kernelInclusion f) := by
  simp [splitPointsEquiv, powerKernelPointsEquiv, torsionKernelPointsEquiv,
    CoprimeKernels.kernelProductEquiv, CoprimeKernels.kernelProductMap,
    Scheme.kernelPointsEquiv, Scheme.kernelInclusion,
    homEquivToProd, Category.assoc]
  exact pullback.lift_fst _ _ _

/-- The splitting is natural on arbitrary test objects. -/
theorem splitPointsEquiv_naturality {T U : C} (a : T ⟶ U)
    (x : U ⟶ Scheme.kernelObject ((𝟙 A) ^ n) ⊗ Scheme.kernelObject f) :
    splitPointsEquiv f n m hnm hker T (a ≫ x) =
      a ≫ splitPointsEquiv f n m hnm hker U x := by
  apply (cancel_mono (Scheme.kernelInclusion (f ^ n))).mp
  rw [Category.assoc, splitPointsEquiv_comp_inclusion, splitPointsEquiv_comp_inclusion,
    MonObj.comp_mul]
  simp only [Category.assoc]

/-- The kernel decomposition is a genuine isomorphism of represented objects. -/
def kernelProductIso :
    Scheme.kernelObject ((𝟙 A) ^ n) ⊗ Scheme.kernelObject f ≅
      Scheme.kernelObject (f ^ n) :=
  Yoneda.fullyFaithful.preimageIso (NatIso.ofComponents
    (fun T => (splitPointsEquiv f n m hnm hker T.unop).toIso)
    (fun a => by ext x; exact splitPointsEquiv_naturality f n m hnm hker a.unop x))

/-- On underlying objects, the splitting is multiplication of the two inclusions. -/
theorem kernelProductIso_hom_comp_inclusion :
    (kernelProductIso f n m hnm hker).hom ≫ Scheme.kernelInclusion (f ^ n) =
      (fst _ _ ≫ Scheme.kernelInclusion ((𝟙 A) ^ n)) *
        (snd _ _ ≫ Scheme.kernelInclusion f) := by
  change splitPointsEquiv f n m hnm hker _ (𝟙 _) ≫
      Scheme.kernelInclusion (f ^ n) = _
  simpa only [Category.id_comp] using
    splitPointsEquiv_comp_inclusion f n m hnm hker _ (𝟙 _)

attribute [local instance] Scheme.kernelGroup

omit [BraidedCategory C] [HasPullbacks C] in
/-- A monomorphism of group objects detects preservation of the group law. -/
theorem isMonHom_of_mono_postcomp {P Q Z : C} [GrpObj P] [GrpObj Q] [GrpObj Z]
    (a : P ⟶ Q) (b : Q ⟶ Z) [Mono b] [IsMonHom b] [IsMonHom (a ≫ b)] :
    IsMonHom a := by
  constructor
  · apply (cancel_mono b).mp
    rw [Category.assoc, IsMonHom.one_hom (a ≫ b), IsMonHom.one_hom b]
  · apply (cancel_mono b).mp
    rw [Category.assoc, IsMonHom.mul_hom (a ≫ b), Category.assoc,
      IsMonHom.mul_hom b, ← Category.assoc, ← tensorHom_comp_tensorHom]

/-- The represented splitting respects the actual group-object laws. -/
theorem kernelProductIso_isMonHom : IsMonHom (kernelProductIso f n m hnm hker).hom := by
  have h : IsMonHom ((kernelProductIso f n m hnm hker).hom ≫
      Scheme.kernelInclusion (f ^ n)) := by
    rw [kernelProductIso_hom_comp_inclusion, Hom.mul_def]
    infer_instance
  exact isMonHom_of_mono_postcomp _ (Scheme.kernelInclusion (f ^ n))

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Splitting
