import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismPrincipal
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.OrdinaryBaseIso
import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.AlgebraPullback

/-! # Morphism Base -/

namespace OAI

noncomputable section

namespace NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismBase.Coordinates

/-! Section-ring coordinates for the finite-model scalar-change square. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p] (n : ℕ)
  {X₁ X₂ : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n)))} [Smooth X₁.hom] [Smooth X₂.hom]
  {Y₁ Y₂ : Over (Spec (CommRingCat.of k))}
  (u : X₁ ⟶ X₂) (v : Y₁ ⟶ Y₂) (f₁ : Y₁.left ⟶ X₁.left) (f₂ : Y₂.left ⟶ X₂.left)
  (hp₁ : IsPullback f₁ Y₁.hom X₁.hom (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (hp₂ : IsPullback f₂ Y₂.hom X₂.hom (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (sq : f₁ ≫ u.left = v.left ≫ f₂)

local notation "W" => WittVector p k
local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.Witt.Ring p k n

def sourceAlgebra (U : AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.Charts u.left) : CommAlgCat R :=
  (Affine.AlgebraPullback.diagram R X₂).obj (op U.val.2)
def targetAlgebra (U : AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.Charts u.left) : CommAlgCat R :=
  (Affine.AlgebraPullback.diagram R X₁).obj (op U.val.1)

local instance sourceWitt (U : AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.Charts u.left) :
    Algebra W (sourceAlgebra p k n u U) :=
  Truncated.SmoothFrame.Complex.wittAlgebra p k n (sourceAlgebra p k n u U)
local instance targetWitt (U : AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.Charts u.left) :
    Algebra W (targetAlgebra p k n u U) :=
  Truncated.SmoothFrame.Complex.wittAlgebra p k n (targetAlgebra p k n u U)
local instance sourceTower (U : AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.Charts u.left) :
    IsScalarTower W R (sourceAlgebra p k n u U) := IsScalarTower.of_algebraMap_eq' rfl
local instance targetTower (U : AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.Charts u.left) :
    IsScalarTower W R (targetAlgebra p k n u U) := IsScalarTower.of_algebraMap_eq' rfl

def integral (U : AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.Charts u.left) :
    sourceAlgebra p k n u U →ₐ[R] targetAlgebra p k n u U :=
  ((Affine.AlgebraPullback.transformation R u).app (op U)).hom

theorem ring_component (U : AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.Charts u.left) :
    (MorphismRings.transformation p k n u v f₁ f₂ hp₁ hp₂ sq).app (op U) =
      CommAlgCat.ofHom ((integral p k n u U).restrictScalars W) := by
  rw [MorphismRings.component]
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  intro x
  rfl

theorem forms_square (U : AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.Charts u.left) (degree : ℕ)
    (ω : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form W (sourceAlgebra p k n u U) degree) :
    OrdinaryBaseQuotient.Ordinary.formsEquiv W R (targetAlgebra p k n u U) Ideal.Quotient.mk_surjective degree
      (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap
        ((MorphismRings.transformation p k n u v f₁ f₂ hp₁ hp₂ sq).app (op U)) degree ω) =
    AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap (CommAlgCat.ofHom (integral p k n u U)) degree
      (OrdinaryBaseQuotient.Ordinary.formsEquiv W R (sourceAlgebra p k n u U) Ideal.Quotient.mk_surjective degree ω) := by
  have h := congrArg (fun a : CommAlgCat.of W (sourceAlgebra p k n u U) ⟶
      CommAlgCat.of W (targetAlgebra p k n u U) => AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap a degree ω)
    (ring_component p k n u v f₁ f₂ hp₁ hp₂ sq U)
  exact (congrArg (OrdinaryBaseQuotient.Ordinary.formsEquiv W R (targetAlgebra p k n u U)
      Ideal.Quotient.mk_surjective degree) h).trans
    (GeometricComparison.SurjectiveBase.SurjectiveBaseDeRham.forms_naturality W R (sourceAlgebra p k n u U)
      Ideal.Quotient.mk_surjective (targetAlgebra p k n u U) (integral p k n u U) degree ω)

end NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismBase.Coordinates

namespace NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismBase.Comparison

/-! The actual finite-level ordinary de Rham comparison commutes with
model morphisms, including its change from Witt scalars to the
truncated coefficient ring. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p] (n : ℕ)
  {X₁ X₂ : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n)))} [Smooth X₁.hom] [Smooth X₂.hom]
  {Y₁ Y₂ : Over (Spec (CommRingCat.of k))}
  (u : X₁ ⟶ X₂) (v : Y₁ ⟶ Y₂) (f₁ : Y₁.left ⟶ X₁.left) (f₂ : Y₂.left ⟶ X₂.left)
  (hp₁ : IsPullback f₁ Y₁.hom X₁.hom (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (hp₂ : IsPullback f₂ Y₂.hom X₂.hom (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (sq : f₁ ≫ u.left = v.left ≫ f₂)

local notation "W" => WittVector p k
local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.Witt.Ring p k n
local notation "S" => Functor.op (OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.source (Over.Hom.left u))
local notation "T" => Functor.op (OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.target (Over.Hom.left u))
local notation "M" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismRings.transformation p k n u v f₁ f₂ hp₁ hp₂ sq

def ordinaryMap : T ⋙ OrdinaryBaseIso.Ordinary.target p k n X₂ ⟶
    S ⋙ OrdinaryBaseIso.Ordinary.target p k n X₁ :=
  Functor.whiskerRight
    (Functor.whiskerRight (Affine.AlgebraPullback.transformation R u)
      (OrdinaryDeRhamFunctor.Ordinary.functor R))
    ((ModuleCat.restrictScalars (algebraMap W R)).mapHomologicalComplex (.up ℕ))

theorem base_component (U : (AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.Charts u.left)ᵒᵖ) :
    OrdinaryDeRhamFunctor.Ordinary.map ((M).app U) ≫
      (OrdinaryBaseIso.Ordinary.component p k n X₁ Y₁ f₁ hp₁ (op U.unop.val.1)).hom =
    (OrdinaryBaseIso.Ordinary.component p k n X₂ Y₂ f₂ hp₂ (op U.unop.val.2)).hom ≫
      (ordinaryMap p k n u).app U := by
  apply HomologicalComplex.Hom.ext
  funext degree
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro ω
  exact Coordinates.forms_square p k n u v f₁ f₂ hp₁ hp₂ sq
    U.unop degree ω

theorem base_natural :
    Functor.whiskerRight M (OrdinaryDeRhamFunctor.Ordinary.functor W) ≫
      Functor.whiskerLeft S (OrdinaryBaseIso.Ordinary.iso p k n X₁ Y₁ f₁ hp₁).hom =
    Functor.whiskerLeft T (OrdinaryBaseIso.Ordinary.iso p k n X₂ Y₂ f₂ hp₂).hom ≫
      ordinaryMap p k n u := by
  apply NatTrans.ext
  funext U
  exact base_component p k n u v f₁ f₂ hp₁ hp₂ sq U

theorem natural :
    MorphismPrincipal.Comparison.frameMap p k n u v f₁ f₂ hp₁ hp₂ sq ≫
      Functor.whiskerLeft S (OrdinaryBaseIso.Ordinary.pdIso p k n X₁ Y₁ f₁ hp₁).hom =
    Functor.whiskerLeft T (OrdinaryBaseIso.Ordinary.pdIso p k n X₂ Y₂ f₂ hp₂).hom ≫
      ordinaryMap p k n u := by
  let a := MorphismPrincipal.Comparison.frameMap p k n u v f₁ f₂ hp₁ hp₂ sq
  let c₁ := Functor.whiskerLeft S (PrincipalComplex.Comparison.iso p k n X₁ Y₁ f₁ hp₁).hom
  let c₂ := Functor.whiskerLeft T (PrincipalComplex.Comparison.iso p k n X₂ Y₂ f₂ hp₂).hom
  let b₁ := Functor.whiskerLeft S (OrdinaryBaseIso.Ordinary.iso p k n X₁ Y₁ f₁ hp₁).hom
  let b₂ := Functor.whiskerLeft T (OrdinaryBaseIso.Ordinary.iso p k n X₂ Y₂ f₂ hp₂).hom
  let m := Functor.whiskerRight M (OrdinaryDeRhamFunctor.Ordinary.functor W)
  change a ≫ (c₁ ≫ b₁) = (c₂ ≫ b₂) ≫ ordinaryMap p k n u
  calc
    a ≫ (c₁ ≫ b₁) = (a ≫ c₁) ≫ b₁ := (Category.assoc _ _ _).symm
    _ = (c₂ ≫ m) ≫ b₁ := congrArg (fun z => z ≫ b₁)
      (MorphismPrincipal.Comparison.natural p k n u v f₁ f₂ hp₁ hp₂ sq)
    _ = c₂ ≫ (m ≫ b₁) := Category.assoc _ _ _
    _ = c₂ ≫ (b₂ ≫ ordinaryMap p k n u) :=
      congrArg (fun z => c₂ ≫ z) (base_natural p k n u v f₁ f₂ hp₁ hp₂ sq)
    _ = (c₂ ≫ b₂) ≫ ordinaryMap p k n u := (Category.assoc _ _ _).symm

end NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismBase.Comparison

end

end OAI
