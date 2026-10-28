import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.ProductFrame
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.PointedFiniteAffineCover
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.Products

/-! # Product Triviality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.ProductTriviality

noncomputable section

/-! The local product triviality criterion with the finite affine
covers and product projective presentation constructed internally. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme.Modules

universe u

theorem localAbelianProduct_line_trivial_of_axes
    {S : Scheme.{u}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)] [IsLocalRing Γ(S, ⊤)]
    {g h : ℕ} (A : Abelian.Schemes.AbelianScheme g S) (B : Abelian.Schemes.AbelianScheme h S)
    (PA : Projective.ProjectivePresentations.ProjectivePresentation A.scheme) (PB : Projective.ProjectivePresentations.ProjectivePresentation B.scheme)
    (sA : S ⟶ A.scheme.left) (hsA : sA ≫ A.scheme.hom = 𝟙 _)
    (sB : S ⟶ B.scheme.left) (hsB : sB ≫ B.scheme.hom = 𝟙 _)
    (L : Line.Bundles.LineBundle (pullback A.scheme.hom B.scheme.hom))
    (eA : (L.pullback (Quotients.FiniteDescent.ProductBaseAxes.Construction.ProductBaseChangeAxes.left A.scheme.hom B.scheme.hom sB hsB)).sheaf ≅
      Line.Bundles.structureModule A.scheme.left)
    (eB : (L.pullback (Quotients.FiniteDescent.ProductBaseAxes.Construction.ProductBaseChangeAxes.right A.scheme.hom B.scheme.hom sA hsA)).sheaf ≅
      Line.Bundles.structureModule B.scheme.left)
    (he : (L.pullback (pullback.fst (pullback.fst A.scheme.hom B.scheme.hom ≫ A.scheme.hom)
      (ReferenceFamily.Affine.CoefficientUnitExactness.coefficientFieldPoint S (IsLocalRing.ResidueField Γ(S, ⊤))))).sheaf ≅
        Line.Bundles.structureModule (pullback (pullback.fst A.scheme.hom B.scheme.hom ≫ A.scheme.hom)
          (ReferenceFamily.Affine.CoefficientUnitExactness.coefficientFieldPoint S (IsLocalRing.ResidueField Γ(S, ⊤))))) :
    Nonempty (L.sheaf ≅ Line.Bundles.structureModule (pullback A.scheme.hom B.scheme.hom)) := by
  have : A.scheme.left.IsSeparated := ⟨by rw [← terminal.comp_from A.scheme.hom]; infer_instance⟩
  have : B.scheme.left.IsSeparated := ⟨by rw [← terminal.comp_from B.scheme.hom]; infer_instance⟩
  have : (pullback A.scheme.hom B.scheme.hom).IsSeparated :=
    ⟨by rw [← terminal.comp_from (pullback.fst A.scheme.hom B.scheme.hom)]; infer_instance⟩
  have : CompactSpace A.scheme.left := QuasiCompact.compactSpace_of_compactSpace A.scheme.hom
  have : CompactSpace B.scheme.left := QuasiCompact.compactSpace_of_compactSpace B.scheme.hom
  let C := PointedFiniteAffineCover.LocalPointedFiniteAffineCover.ofLocalBase sA
  let D := PointedFiniteAffineCover.LocalPointedFiniteAffineCover.ofLocalBase sB
  let := C.fintype
  let := C.linearOrder
  let := D.fintype
  let := D.linearOrder
  exact ProductFrame.localAbelianProduct_line_trivial A B PA PB (PA.product PB)
    C.opens D.opens C.affine D.affine C.covers D.covers sA hsA sB hsB
    C.distinguished C.point_in D.distinguished D.point_in L eA eB he

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.ProductTriviality
