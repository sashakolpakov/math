import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.WeilCoverRefinement

/-! # Polarization Weil Compatibility -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PolarizationWeilCompatibility

noncomputable section

/-! Compatibility of the actual polarization Weil pairing under
simultaneous multiplication on both torsion arguments. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
  (A : Over (Spec (.of k))) [GrpObj A] [IsCommMonObj A]
  [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
  (D : Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData A) (ell : A ⟶ D.abelian) [IsMonHom ell]
  [IsFinite ell.left] [Flat ell.left] [Surjective ell.left]
  (n : ℕ) (hn : 0 < n)
  (hdegree : ∀ s : Spec (.of k), n.Coprime (ell.left.finrank (η[D.abelian].left s)))

theorem geometricIsogenyTorsionPairing_value (T : Over (Spec (.of k)))
    (x y : T ⟶ IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme A n) :
    (IsogenyQuotient.Geometric.WeilPairing.Construction.geometricIsogenyTorsionPairing A D ell n hn hdegree).pairValue x y =
      (IsogenyQuotient.Geometric.WeilPairing.Construction.geometricNativeWeilPairing A D ell n hn hdegree).pairValue x (y ≫ IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap n ell) := by
  change ((IsogenyQuotient.Geometric.WeilPairing.Construction.geometricNativeWeilPairing A D ell n hn hdegree).restrict (𝟙 _) (IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap n ell)).pairValue x y = _
  rw [IsogenyQuotient.Annihilator.Construction.SchemeBicharacter.restrict_pairValue, Category.comp_id]

variable (N : ℕ) (hN : 0 < N)
  (hdegreeN : ∀ s : Spec (.of k), N.Coprime (ell.left.finrank (η[D.abelian].left s)))
  (m : ℕ) (hm : m * n = N)

include hm in
theorem geometricIsogenyTorsionPairing_power_refinement (T : Over (Spec (.of k)))
    (x y : T ⟶ IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme A n) (x' y' : T ⟶ IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme A N)
    (hx : (x' ≫ IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion A N) ^ m = x ≫ IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion A n)
    (hy : (y' ≫ IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion A N) ^ m = y ≫ IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion A n) :
    ((IsogenyQuotient.Geometric.WeilPairing.Construction.geometricIsogenyTorsionPairing A D ell N hN hdegreeN).pairValue x' y') ^ m =
      (IsogenyQuotient.Geometric.WeilPairing.Construction.geometricIsogenyTorsionPairing A D ell n hn hdegree).pairValue x y := by
  have hi (r : ℕ) (z : T ⟶ IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme A r) :
      (z ≫ IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap r ell) ≫ IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion D.abelian r =
        (z ≫ IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion A r) ≫ ell := by
    rw [Category.assoc, IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap_inclusion, ← Category.assoc]
  have hye : ((y' ≫ IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap N ell) ≫ IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion D.abelian N) ^ m =
      (y ≫ IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap n ell) ≫ IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion D.abelian n :=
    (congrArg (fun z => z ^ m) (hi N y')).trans
      ((MonObj.pow_comp (y' ≫ IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion A N) m ell).symm.trans
        ((congrArg (fun z => z ≫ ell) hy).trans (hi n y).symm))
  rw [geometricIsogenyTorsionPairing_value, geometricIsogenyTorsionPairing_value]
  exact WeilCoverRefinement.nativeWeilPairing_power_refinement A D ell n hn hdegree N hN hdegreeN m hm T
    x x' (y ≫ IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap n ell) (y' ≫ IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap N ell) hx hye

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PolarizationWeilCompatibility
