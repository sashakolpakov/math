import OAI.AlgebraicGeometry.CycleClass.Thom.AffineGraphAmbient
import OAI.AlgebraicGeometry.CycleClass.Thom.SmoothAffineGlobalCoordinates
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.FiniteTypeSchemeTopology

/-! # Scheme Graph -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SchemeGraph.Constructions

noncomputable section

/-! An actual map between affine complex schemes admits a genuine polynomial graph factorization over its prescribed target. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

open OAI.AlgebraicGeometry.CycleClass.Thom.Affine.GraphScheme.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.AffineGraphAmbient.Constructions.Scheme OAI.AlgebraicGeometry.CycleClass.Thom.Affine.PresentationImmersion.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsAffine X.left] [IsAffine Y.left]
  (g : X ⟶ Y) {n : ℕ} (f : MvPolynomial (Fin n) ℂ →ₐ[ℂ] Γ(X.left, ⊤))

def globalGraphSchemeMap : X ⟶ Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ (Γ(Y.left, ⊤) ⊗[ℂ] MvPolynomial (Fin n) ℂ) :=
  (Foundations.Scheme.AffineSchemeComplexPoints.affineOverIso X).hom ≫ GraphScheme.Constructions.graphSchemeMap (ComplexPoints.Analytic.AffineSchemePointTopology.affineCoordinateHom g) f

theorem globalGraphSchemeMap_closedImmersion (hf : Function.Surjective f) :
    IsClosedImmersion (globalGraphSchemeMap g f).left := by
  let : IsClosedImmersion (GraphScheme.Constructions.graphSchemeMap (ComplexPoints.Analytic.AffineSchemePointTopology.affineCoordinateHom g) f).left :=
    GraphScheme.Constructions.graphSchemeMap_closedImmersion (ComplexPoints.Analytic.AffineSchemePointTopology.affineCoordinateHom g) f hf
  change IsClosedImmersion ((Foundations.Scheme.AffineSchemeComplexPoints.affineOverIso X).hom.left ≫ (GraphScheme.Constructions.graphSchemeMap (ComplexPoints.Analytic.AffineSchemePointTopology.affineCoordinateHom g) f).left)
  infer_instance

theorem globalGraphSchemeMap_projection :
    globalGraphSchemeMap g f ≫
      Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ Γ(Y.left, ⊤) (Γ(Y.left, ⊤) ⊗[ℂ] MvPolynomial (Fin n) ℂ)
        Algebra.TensorProduct.includeLeft ≫ (Foundations.Scheme.AffineSchemeComplexPoints.affineOverIso Y).inv = g := by
  rw [globalGraphSchemeMap, Category.assoc, ← Category.assoc (GraphScheme.Constructions.graphSchemeMap _ _),
    GraphScheme.Constructions.graphSchemeMap_left, ComplexPoints.Analytic.AffineSchemePointTopology.affineAlgHomOverSpecEquiv_affineCoordinateHom]
  simp only [Category.assoc, Iso.hom_inv_id_assoc,
    Iso.hom_inv_id, Category.comp_id]

theorem globalGraphSchemeMap_point (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) :
    AffineGraphAmbient.Constructions.Scheme.schemeGraphHomeomorph Γ(Y.left, ⊤) n (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (globalGraphSchemeMap g f) x) =
      (ComplexPoints.Analytic.AffineSchemePointTopology.affineNativePointHomeomorph Y (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g x),
        PresentationImmersion.Constructions.presentationCoordinates f (ComplexPoints.Analytic.AffineSchemePointTopology.affineNativePointHomeomorph X x)) := by
  change AffineGraphAmbient.Constructions.Scheme.schemeGraphHomeomorph Γ(Y.left, ⊤) n
    (x ≫ ((Foundations.Scheme.AffineSchemeComplexPoints.affineOverIso X).hom ≫ GraphScheme.Constructions.graphSchemeMap (ComplexPoints.Analytic.AffineSchemePointTopology.affineCoordinateHom g) f)) = _
  rw [← Category.assoc, ← ComplexPoints.Analytic.AffineSchemePointTopology.affineSchemePointEquiv_affineNativePointHomeomorph X x]
  exact (AffineGraphAmbient.Constructions.Scheme.schemeGraphHomeomorph_graph Γ(Y.left, ⊤) n (ComplexPoints.Analytic.AffineSchemePointTopology.affineCoordinateHom g) f
    (ComplexPoints.Analytic.AffineSchemePointTopology.affineNativePointHomeomorph X x)).trans
    (congrArg (fun a => (a, PresentationImmersion.Constructions.presentationCoordinates f (ComplexPoints.Analytic.AffineSchemePointTopology.affineNativePointHomeomorph X x)))
      (ComplexPoints.Analytic.AffineSchemePointTopology.affineNativePointHomeomorph_map g x).symm)

theorem exists_globalGraphSchemeMap [LocallyOfFiniteType X.hom] :
    ∃ (n : ℕ) (f : MvPolynomial (Fin n) ℂ →ₐ[ℂ] Γ(X.left, ⊤)),
      Function.Surjective f ∧ IsClosedImmersion (globalGraphSchemeMap g f).left := by
  let : Algebra.FiniteType ℂ Γ(X.left, ⊤) := ComplexPoints.Analytic.FiniteTypeSchemeTopology.affineOverGamma_finiteType X
  obtain ⟨n, f, hf⟩ :=
    (Algebra.FiniteType.iff_quotient_mvPolynomial'' (R := ℂ) (S := Γ(X.left, ⊤))).mp inferInstance
  exact ⟨n, f, hf, globalGraphSchemeMap_closedImmersion g f hf⟩

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SchemeGraph.Constructions
