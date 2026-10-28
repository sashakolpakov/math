import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.WeilNaturalityCover
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PolarizationWeilCompatibility

/-! # Polarization Weil Naturality -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PolarizationWeilNaturality

noncomputable section

/-! Original polarization equations imply similitude and adjoint
identities for the canonical finite Weil pairing on every test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

section Points
variable {S : Scheme.{u}} (A B : Over S) [GrpObj A] [IsCommMonObj A]
  [GrpObj B] [IsCommMonObj B] (f : A ⟶ B) [IsMonHom f] (n : ℕ)

theorem nativeTorsionPoint_map_inclusion (T : Over S) (x : T ⟶ IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme A n) :
    (x ≫ IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap n f) ≫ IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion B n =
      (x ≫ IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion A n) ≫ f := by
  rw [Category.assoc, IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap_inclusion, ← Category.assoc]

end Points

section Similitude
variable {k : Type u} [Field k] [IsAlgClosed k]
  (A A' : Over (Spec (.of k)))
  [GrpObj A] [IsCommMonObj A] [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
  [GrpObj A'] [IsCommMonObj A'] [Smooth A'.hom] [IsProper A'.hom] [GeometricallyConnected A'.hom]
  (D : Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData A) (D' : Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData A')
  (ell : A ⟶ D.abelian) [IsMonHom ell] [IsFinite ell.left] [Flat ell.left] [Surjective ell.left]
  (ell' : A' ⟶ D'.abelian) [IsMonHom ell'] [IsFinite ell'.left] [Flat ell'.left] [Surjective ell'.left]
  (n : ℕ) (hn : 0 < n)
  (hdegree : ∀ s : Spec (.of k), n.Coprime (ell.left.finrank (η[D.abelian].left s)))
  (hdegree' : ∀ s : Spec (.of k), n.Coprime (ell'.left.finrank (η[D'.abelian].left s)))
  (t : A' ⟶ A) [IsMonHom t] (d : D.abelian ⟶ D'.abelian)
  (hd : d = Picard.Homomorphisms.UnbundledDualPullback.Construction.UnbundledPicard.dualPicardPullback D' D t) (m : ℕ) (hpol : t ≫ ell ≫ d = ell' ^ m)

include hpol in
omit [IsAlgClosed k] [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
  [Smooth A'.hom] [IsProper A'.hom] [GeometricallyConnected A'.hom]
  [IsFinite ell.left] [Flat ell.left] [Surjective ell.left]
  [IsFinite ell'.left] [Flat ell'.left] [Surjective ell'.left] in
theorem polarizationTorsionPoint_similitude (T : Over (Spec (.of k)))
    (y : T ⟶ IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme A' n) :
    (((y ≫ IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap n t) ≫ IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap n ell) ≫ IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion D.abelian n) ≫ d =
      ((y ≫ IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap n ell') ^ m) ≫ IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion D'.abelian n := by
  rw [nativeTorsionPoint_map_inclusion, nativeTorsionPoint_map_inclusion]
  rw [Category.assoc, Category.assoc, hpol, MonObj.comp_pow]
  rw [MonObj.pow_comp, nativeTorsionPoint_map_inclusion]

include hd hpol in
theorem geometricIsogenyTorsionPairing_similitude (T : Over (Spec (.of k)))
    (x y : T ⟶ IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme A' n) :
    (IsogenyQuotient.Geometric.WeilPairing.Construction.geometricIsogenyTorsionPairing A D ell n hn hdegree).pairValue
        (x ≫ IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap n t) (y ≫ IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap n t) =
      ((IsogenyQuotient.Geometric.WeilPairing.Construction.geometricIsogenyTorsionPairing A' D' ell' n hn hdegree').pairValue x y) ^ m := by
  have he := WeilNaturalityCover.nativeWeilPairing_natural A A' D D' ell ell' n hn hdegree hdegree' t d hd T
    (x ≫ IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap n t) x
    ((y ≫ IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap n t) ≫ IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap n ell) ((y ≫ IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap n ell') ^ m)
    (nativeTorsionPoint_map_inclusion A' A t n T x).symm
    (polarizationTorsionPoint_similitude A A' D D' ell ell' n t d m hpol T y)
  rw [PolarizationWeilCompatibility.geometricIsogenyTorsionPairing_value, PolarizationWeilCompatibility.geometricIsogenyTorsionPairing_value]
  exact he.symm.trans (((IsogenyQuotient.Geometric.WeilPairing.Construction.geometricNativeWeilPairing A' D' ell' n hn hdegree').pairRightHom x).map_pow _ m)

end Similitude

variable {k : Type u} [Field k] [IsAlgClosed k]
  (A : Over (Spec (.of k)))
  [GrpObj A] [IsCommMonObj A] [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
  (D : Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData A)
  (ell : A ⟶ D.abelian) [IsMonHom ell] [IsFinite ell.left] [Flat ell.left] [Surjective ell.left]
  (n : ℕ) (hn : 0 < n)
  (hdegree : ∀ s : Spec (.of k), n.Coprime (ell.left.finrank (η[D.abelian].left s)))
  (t c : A ⟶ A) [IsMonHom t] [IsMonHom c] (d : D.abelian ⟶ D.abelian)
  (hd : d = Picard.Homomorphisms.UnbundledDualPullback.Construction.UnbundledPicard.dualPicardPullback D D t) (hpol : ell ≫ d = c ≫ ell)

include hd hpol in
theorem geometricIsogenyTorsionPairing_adjoint (T : Over (Spec (.of k)))
    (x y : T ⟶ IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme A n) :
    (IsogenyQuotient.Geometric.WeilPairing.Construction.geometricIsogenyTorsionPairing A D ell n hn hdegree).pairValue (x ≫ IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap n t) y =
      (IsogenyQuotient.Geometric.WeilPairing.Construction.geometricIsogenyTorsionPairing A D ell n hn hdegree).pairValue x (y ≫ IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap n c) := by
  have hy : ((y ≫ IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap n ell) ≫ IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion D.abelian n) ≫ d =
      ((y ≫ IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap n c) ≫ IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap n ell) ≫ IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion D.abelian n := by
    rw [nativeTorsionPoint_map_inclusion, nativeTorsionPoint_map_inclusion,
      nativeTorsionPoint_map_inclusion, Category.assoc, hpol, ← Category.assoc]
  have he := WeilNaturalityCover.nativeWeilPairing_natural A A D D ell ell n hn hdegree hdegree t d hd T
    (x ≫ IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap n t) x (y ≫ IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap n ell)
    ((y ≫ IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap n c) ≫ IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap n ell)
    (nativeTorsionPoint_map_inclusion A A t n T x).symm hy
  rw [PolarizationWeilCompatibility.geometricIsogenyTorsionPairing_value, PolarizationWeilCompatibility.geometricIsogenyTorsionPairing_value]
  exact he.symm

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PolarizationWeilNaturality
