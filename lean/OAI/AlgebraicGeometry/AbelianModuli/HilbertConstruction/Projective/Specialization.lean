import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.FiberPolynomial

/-! # Specialization -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Hilbert polynomials of flat projective fibers over a locally Noetherian base are unchanged by specialization. Both fibers are compared inside the actual local-ring base change. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

theorem Closed.Families.FlatClosedFamily.fiberHilbertPolynomial_eq_of_specializes
    {S : Scheme.{u}} [IsLocallyNoetherian S] {n : ℕ}
    (F : Closed.Families.FlatClosedFamily (Projective.ProjectivePresentations.projectiveSpaceOver S n)) {x y : S} (h : x ⤳ y) :
    F.fiberHilbertPolynomial x = F.fiberHilbertPolynomial y := by
  let R := S.presheaf.stalk y
  have hR : IsNoetherianRing R :=
    AlgebraicGeometry.instIsNoetherianRingCarrierStalkCommRingCatPresheafOfIsLocallyNoetherian
      (X := S) (x := y)
  have hlocal : IsLocalRing R := S.toLocallyRingedSpace.isLocalRing y
  let b := S.fromSpecStalk y
  let G := F.projectiveBaseChange b
  obtain ⟨P, hP⟩ := @Closed.Families.FlatClosedFamily.exists_localFieldHilbertPolynomial R _ hR hlocal n G
  let tx : Spec (S.residueField x) ⟶ Spec R :=
    Spec.map (S.presheaf.stalkSpecializes h ≫ S.residue x)
  let ty : Spec (S.residueField y) ⟶ Spec R := Spec.map (S.residue y)
  have hx : tx ≫ b = S.fromSpecResidueField x := by
    change Spec.map (S.presheaf.stalkSpecializes h ≫ S.residue x) ≫ S.fromSpecStalk y = _
    rw [Spec.map_comp, Category.assoc, S.SpecMap_stalkSpecializes_fromSpecStalk h]
    rfl
  have hy : ty ≫ b = S.fromSpecResidueField y := rfl
  have hpx := hP (S.residueField x) tx
  have hpy := hP (S.residueField y) ty
  have hFx := (F.projectiveBaseChange_affine b tx).trans
    (congrArg (fun s => F.affineProjectivePullback s) hx)
  have hFy := (F.projectiveBaseChange_affine b ty).trans
    (congrArg (fun s => F.affineProjectivePullback s) hy)
  rw [hFx] at hpx
  rw [hFy] at hpy
  exact (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.hilbertPolynomial_unique (F.fiberHilbertPolynomial_spec x) hpx).trans
    (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.hilbertPolynomial_unique (F.fiberHilbertPolynomial_spec y) hpy).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
