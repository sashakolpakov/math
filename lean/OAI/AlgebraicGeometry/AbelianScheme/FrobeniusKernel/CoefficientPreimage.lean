import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CoefficientTargetSubgroup
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.SubgroupPreimageProjector
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.SubgroupPreimageGeometry
import OAI.AlgebraicGeometry.PELModuli.CMPoints.BlockDecomposition
import OAI.AlgebraicGeometry.Picard.Homomorphisms.FinitePresentation

/-! # Coefficient Preimage -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CoefficientPreimage.Construction

noncomputable section

section

/-! The actual O_E-linear isogeny gives a coefficient-preserving
preimage cover. Its source torsion bound proves projector idempotence. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
  {S : Scheme} {g h : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h S)
  (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A)
  (σ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) B)
  (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B)
  (hσ : ∀ a, ρ.map a ≫ f.hom = f.hom ≫ σ.map a)
  (τ : Gal(E/ℚ)) {J : Grp (Over S)}
  (i : J ⟶ (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit B σ 1 τ).toGrp)

abbrev coefficientPreimage : Grp (Over S) :=
  SubgroupPreimage.Construction.subgroupPreimage (Grp.homMk (A := Grp.mk A.scheme) (B := Grp.mk B.scheme) f.hom) (CoefficientTargetSubgroup.Construction.coefficientTargetInclusion j iota hsplit B σ τ i)

abbrev coefficientPreimageInclusion : coefficientPreimage j iota hsplit A B σ f τ i ⟶ Grp.mk A.scheme :=
  SubgroupPreimage.Construction.subgroupPreimageInclusion (Grp.homMk (A := Grp.mk A.scheme) (B := Grp.mk B.scheme) f.hom) (CoefficientTargetSubgroup.Construction.coefficientTargetInclusion j iota hsplit B σ τ i)

abbrev coefficientPreimageProjection : coefficientPreimage j iota hsplit A B σ f τ i ⟶ J :=
  SubgroupPreimage.Construction.subgroupPreimageProjection (Grp.homMk (A := Grp.mk A.scheme) (B := Grp.mk B.scheme) f.hom) (CoefficientTargetSubgroup.Construction.coefficientTargetInclusion j iota hsplit B σ τ i)

variable (n : ℕ)

def coefficientPreimageProjector : coefficientPreimage j iota hsplit A B σ f τ i ⟶
    coefficientPreimage j iota hsplit A B σ f τ i :=
  SubgroupPreimageProjector.Construction.subgroupPreimageEndomorphism (Grp.homMk (A := Grp.mk A.scheme) (B := Grp.mk B.scheme) f.hom) (CoefficientTargetSubgroup.Construction.coefficientTargetInclusion j iota hsplit B σ τ i)
    (Grp.homMk (A := Grp.mk A.scheme) (B := Grp.mk A.scheme) (ρ.map (j.projector iota hsplit (n + 1) τ)))
    (Grp.homMk (A := Grp.mk B.scheme) (B := Grp.mk B.scheme) (σ.map (j.projector iota hsplit (n + 1) τ)))
    (by apply Grp.hom_ext; exact hσ _) (by
      apply Grp.hom_ext
      exact CoefficientTargetSubgroup.Construction.coefficientTargetInclusion_fixed j iota hsplit B σ τ i n)

theorem coefficientPreimageProjector_projection :
    coefficientPreimageProjector j iota hsplit A B ρ σ f hσ τ i n ≫
      coefficientPreimageProjection j iota hsplit A B σ f τ i =
      coefficientPreimageProjection j iota hsplit A B σ f τ i :=
  SubgroupPreimageProjector.Construction.subgroupPreimageEndomorphism_projection _ _ _ _ _ _

theorem coefficientPreimageProjector_inclusion :
    coefficientPreimageProjector j iota hsplit A B ρ σ f hσ τ i n ≫
      coefficientPreimageInclusion j iota hsplit A B σ f τ i =
      coefficientPreimageInclusion j iota hsplit A B σ f τ i ≫
        Grp.homMk (A := Grp.mk A.scheme) (B := Grp.mk A.scheme) (ρ.map (j.projector iota hsplit (n + 1) τ)) :=
  SubgroupPreimageProjector.Construction.subgroupPreimageEndomorphism_inclusion _ _ _ _ _ _

variable (hf : ∀ (T : Over S) (x : T ⟶ A.scheme), x ≫ f.hom = 1 → x ^ (q ^ n) = 1)

include hf in
theorem coefficientPreimage_killed :
    (coefficientPreimageInclusion j iota hsplit A B σ f τ i).hom.hom ^ (q ^ (n + 1)) = 1 := by
  have h := SubgroupPreimage.Construction.subgroupPreimage_killed (Grp.homMk (A := Grp.mk A.scheme) (B := Grp.mk B.scheme) f.hom)
    (CoefficientTargetSubgroup.Construction.coefficientTargetInclusion j iota hsplit B σ τ i) q (q ^ n)
    (CoefficientTargetSubgroup.Construction.coefficientTargetInclusion_killed j iota hsplit B σ τ i) hf
  simpa only [pow_succ'] using h

include hf in
theorem coefficientPreimageProjector_idempotent :
    coefficientPreimageProjector j iota hsplit A B ρ σ f hσ τ i n ≫
      coefficientPreimageProjector j iota hsplit A B ρ σ f hσ τ i n =
      coefficientPreimageProjector j iota hsplit A B ρ σ f hσ τ i n := by
  unfold coefficientPreimageProjector
  apply SubgroupPreimageProjector.Construction.subgroupPreimageEndomorphism_idempotent
  apply Grp.hom_ext
  exact PELModuli.CMPoints.BlockDecomposition.projector_idempotent_on_torsion j iota hsplit A ρ (n + 1) τ
    (coefficientPreimage j iota hsplit A B σ f τ i).X
    (coefficientPreimageInclusion j iota hsplit A B σ f τ i).hom.hom
    (coefficientPreimage_killed j iota hsplit A B σ f τ i n hf)

end

/-! Geometry of the actual coefficient preimage, with the source
isogeny's properties retained on its bundled group morphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
  {S : Scheme} {g h : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h S)
  (σ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) B)
  (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B) (τ : Gal(E/ℚ)) {J : Grp (Over S)}
  (i : J ⟶ (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit B σ 1 τ).toGrp)

theorem coefficientPreimageProjection_cover :
    IsFinite (coefficientPreimageProjection j iota hsplit A B σ f τ i).hom.hom.left ∧
      Flat (coefficientPreimageProjection j iota hsplit A B σ f τ i).hom.hom.left ∧
      LocallyOfFinitePresentation (coefficientPreimageProjection j iota hsplit A B σ f τ i).hom.hom.left ∧
      Surjective (coefficientPreimageProjection j iota hsplit A B σ f τ i).hom.hom.left := by
  let F : Grp.mk A.scheme ⟶ Grp.mk B.scheme := Grp.homMk f.hom
  have : IsFinite F.hom.hom.left := f.finite
  have : Flat F.hom.hom.left := f.flat
  have : Surjective F.hom.hom.left := f.surjective
  have hA : LocallyOfFinitePresentation A.scheme.hom := inferInstance
  have hcomp : LocallyOfFinitePresentation (f.hom.left ≫ B.scheme.hom) :=
    (congrArg LocallyOfFinitePresentation f.hom.w).mpr hA
  have hfp : LocallyOfFinitePresentation f.hom.left :=
    Picard.Homomorphisms.FinitePresentation.Construction.locallyOfFinitePresentation_of_comp_of_finiteType
      hcomp (inferInstanceAs (LocallyOfFiniteType B.scheme.hom))
  have : LocallyOfFinitePresentation F.hom.hom.left := hfp
  exact SubgroupPreimage.Construction.subgroupPreimageProjection_cover F (CoefficientTargetSubgroup.Construction.coefficientTargetInclusion j iota hsplit B σ τ i)

theorem coefficientPreimage_finite [IsFinite J.X.hom] :
    IsFinite (coefficientPreimage j iota hsplit A B σ f τ i).X.hom := by
  let F : Grp.mk A.scheme ⟶ Grp.mk B.scheme := Grp.homMk f.hom
  have : IsFinite F.hom.hom.left := f.finite
  exact SubgroupPreimageGeometry.Construction.subgroupPreimage_finite F (CoefficientTargetSubgroup.Construction.coefficientTargetInclusion j iota hsplit B σ τ i)

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CoefficientPreimage.Construction
