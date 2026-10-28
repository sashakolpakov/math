import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Unit
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.GroupMaps
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Epi

/-! # Groups -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction

noncomputable section

/-!
Actual commutative group schemes for TorsionQuotient's torsion kernels. The kernel
group law is transferred from its represented point functor, and the
equalizer/kernel comparison preserves the inclusion into the abelian
scheme. This connects the torsion-block pairings to subgroup geometry.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

variable {S : Scheme.{u}} (A : Over S) [GrpObj A] [IsCommMonObj A] (n : ℕ)

local instance multiplication_isMonHom : IsMonHom ((𝟙 A) ^ n) :=
  Picard.PoincareBundle.Epi.Construction.isMonHom_pow (𝟙 A) n

/-- The scheme-theoretic torsion kernel with the actual group law. -/
def nativeTorsionScheme : Over S := Picard.PoincareBundle.Kernel.Scheme.kernelObject ((𝟙 A) ^ n)

instance nativeTorsionScheme_group : GrpObj (nativeTorsionScheme A n) :=
  Picard.PoincareBundle.Kernel.Scheme.kernelGroup ((𝟙 A) ^ n)

instance nativeTorsionScheme_commutative : IsCommMonObj (nativeTorsionScheme A n) :=
  Picard.PoincareBundle.Kernel.Scheme.kernelGroup_commutative ((𝟙 A) ^ n)

def nativeTorsionInclusion : nativeTorsionScheme A n ⟶ A :=
  Picard.PoincareBundle.Kernel.Scheme.kernelInclusion ((𝟙 A) ^ n)

instance nativeTorsionInclusion_mono : Mono (nativeTorsionInclusion A n) :=
  inferInstanceAs (Mono (Picard.PoincareBundle.Kernel.Scheme.kernelInclusion ((𝟙 A) ^ n)))

instance nativeTorsionInclusion_isMonHom : IsMonHom (nativeTorsionInclusion A n) :=
  Picard.PoincareBundle.Kernel.Scheme.kernelInclusion_isMonHom ((𝟙 A) ^ n)

theorem nativeTorsionInclusion_killed : (nativeTorsionInclusion A n) ^ n = 1 := by
  change (Picard.PoincareBundle.Kernel.Scheme.kernelInclusion ((𝟙 A) ^ n)) ^ n = 1
  simpa only [MonObj.comp_pow, Category.comp_id] using
    Picard.PoincareBundle.Kernel.Scheme.kernelInclusion_comp ((𝟙 A) ^ n)

def nativeTorsionLift {T : Over S} (a : T ⟶ A) (ha : a ^ n = 1) :
    T ⟶ nativeTorsionScheme A n :=
  (Picard.PoincareBundle.Kernel.Scheme.kernelPointsEquiv ((𝟙 A) ^ n) T).symm
    ⟨a, by
      change a ≫ ((𝟙 A) ^ n) = 1
      simpa only [MonObj.comp_pow, Category.comp_id] using ha⟩

@[simp]
theorem nativeTorsionLift_inclusion {T : Over S} (a : T ⟶ A) (ha : a ^ n = 1) :
    nativeTorsionLift A n a ha ≫ nativeTorsionInclusion A n = a :=
  pullback.lift_fst _ _ _

set_option backward.isDefEq.respectTransparency false in
/-- The group kernel is canonically TorsionQuotient's actual torsion equalizer. -/
def torsionEqualizerKernelIso : TorsionQuotient.SubgroupFunctor.torsionScheme A n ≅ nativeTorsionScheme A n := by
  have hj : (TorsionQuotient.SubgroupFunctor.torsionι A n) ^ n = 1 :=
    (TorsionQuotient.SubgroupFunctor.factors_through_torsion_iff n (TorsionQuotient.SubgroupFunctor.torsionι A n)).mp
      ⟨𝟙 _, Category.id_comp _⟩
  have : Mono (TorsionQuotient.SubgroupFunctor.torsionι A n) :=
    equalizer.ι_mono (f := (𝟙 A) ^ n) (g := (1 : A ⟶ A))
  let d := nativeTorsionLift A n (TorsionQuotient.SubgroupFunctor.torsionι A n) hj
  let c := TorsionQuotient.SubgroupFunctor.torsionLift n (nativeTorsionInclusion A n) (nativeTorsionInclusion_killed A n)
  refine ⟨d, c, ?_, ?_⟩
  · apply (cancel_mono (TorsionQuotient.SubgroupFunctor.torsionι A n)).mp
    simp only [Category.assoc, c, TorsionQuotient.SubgroupFunctor.torsionLift_ι, d,
      nativeTorsionLift_inclusion, Category.id_comp]
  · apply (cancel_mono (nativeTorsionInclusion A n)).mp
    simp only [Category.assoc, d, nativeTorsionLift_inclusion, c,
      TorsionQuotient.SubgroupFunctor.torsionLift_ι, Category.id_comp]

theorem nativeTorsionScheme_finite_etale
    (h_TorsionQuotient : IsFinite (TorsionQuotient.SubgroupFunctor.torsionScheme A n).hom ∧ Etale (TorsionQuotient.SubgroupFunctor.torsionScheme A n).hom) :
    IsFinite (nativeTorsionScheme A n).hom ∧ Etale (nativeTorsionScheme A n).hom := by
  have : IsFinite (TorsionQuotient.SubgroupFunctor.torsionScheme A n).hom := h_TorsionQuotient.1
  have : Etale (TorsionQuotient.SubgroupFunctor.torsionScheme A n).hom := h_TorsionQuotient.2
  have : IsIso (torsionEqualizerKernelIso A n).inv.left :=
    (Over.forget S).map_isIso (torsionEqualizerKernelIso A n).inv
  rw [← (torsionEqualizerKernelIso A n).inv.w]
  exact ⟨inferInstance, inferInstance⟩

variable {A} {B : Over S} [GrpObj B] [IsCommMonObj B]

/-- A homomorphism restricts to the native torsion kernels. -/
def nativeTorsionMap (f : A ⟶ B) [IsMonHom f] :
    nativeTorsionScheme A n ⟶ nativeTorsionScheme B n :=
  nativeTorsionLift B n (nativeTorsionInclusion A n ≫ f) (by
    rw [← MonObj.pow_comp, nativeTorsionInclusion_killed, MonObj.one_comp])

@[simp]
theorem nativeTorsionMap_inclusion (f : A ⟶ B) [IsMonHom f] :
    nativeTorsionMap n f ≫ nativeTorsionInclusion B n = nativeTorsionInclusion A n ≫ f :=
  nativeTorsionLift_inclusion _ _ _ _

instance nativeTorsionMap_isMonHom (f : A ⟶ B) [IsMonHom f] :
    IsMonHom (nativeTorsionMap n f) := by
  apply GroupMaps.Construction.isMonHom_of_pointwise
  · intro T
    apply (cancel_mono (nativeTorsionInclusion B n)).mp
    rw [Category.assoc, nativeTorsionMap_inclusion, ← Category.assoc,
      MonObj.one_comp, MonObj.one_comp, MonObj.one_comp]
  · intro T x y
    apply (cancel_mono (nativeTorsionInclusion B n)).mp
    simp only [Category.assoc, nativeTorsionMap_inclusion, MonObj.mul_comp]

theorem nativeTorsionMap_id : nativeTorsionMap n (𝟙 A) = 𝟙 (nativeTorsionScheme A n) := by
  apply (cancel_mono (nativeTorsionInclusion A n)).mp
  simp only [nativeTorsionMap_inclusion, Category.comp_id, Category.id_comp]

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction
