import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PairingValue

/-! # Weil Naturality -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.WeilNaturality

noncomputable section

/-! Original polarization equations imply the multiplier and adjoint
identities for the actual integral Tate Weil pairing. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u
section Similitude
variable {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
  (A A' : Over (Spec (.of k)))
  [GrpObj A] [IsCommMonObj A] [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
  [GrpObj A'] [IsCommMonObj A'] [Smooth A'.hom] [IsProper A'.hom] [GeometricallyConnected A'.hom]
  (D : Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData A) (D' : Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData A')
  (ell : A ⟶ D.abelian) [IsMonHom ell] [IsFinite ell.left] [Flat ell.left] [Surjective ell.left]
  (ell' : A' ⟶ D'.abelian) [IsMonHom ell'] [IsFinite ell'.left] [Flat ell'.left] [Surjective ell'.left]
  (q : ℕ) [Fact q.Prime]
  (hdegree : ∀ (n : ℕ) (s : Spec (.of k)), (q ^ n).Coprime (ell.left.finrank (η[D.abelian].left s)))
  (hdegree' : ∀ (n : ℕ) (s : Spec (.of k)), (q ^ n).Coprime (ell'.left.finrank (η[D'.abelian].left s)))
  (t : A' ⟶ A) [IsMonHom t] (d : D.abelian ⟶ D'.abelian)
  (hd : d = Picard.Homomorphisms.UnbundledDualPullback.Construction.UnbundledPicard.dualPicardPullback D' D t) (m : ℕ) (hpol : t ≫ ell ≫ d = ell' ^ m)

include hd hpol in
theorem isogenyTateWeilResidues_similitude (n : ℕ)
    (x y : Add.schemeTateModule A' (Over.mk (𝟙 (Spec (.of k)))) q) :
    WeilValues.isogenyTateWeilResidues A D ell q hdegree n
        (Add.schemeTateMap A' _ q t x) (Add.schemeTateMap A' _ q t y) =
      m • WeilValues.isogenyTateWeilResidues A' D' ell' q hdegree' n x y := by
  apply PairingValue.tateBicharacterResidues_eq_nsmul_of_values
  rw [PairingValue.nativeTatePoint_map, PairingValue.nativeTatePoint_map]
  exact PolarizationWeilNaturality.geometricIsogenyTorsionPairing_similitude A A' D D' ell ell' (q ^ n)
    (pow_pos (Fact.out : q.Prime).pos n) (hdegree n) (hdegree' n) t d hd m hpol _ _ _

include hd hpol in
theorem isogenyTateWeilPairing_similitude
    (x y : Add.schemeTateModule A' (Over.mk (𝟙 (Spec (.of k)))) q) :
    WeilValues.isogenyTateWeilPairing A D ell q hdegree
        (Add.schemeTateMap A' _ q t x) (Add.schemeTateMap A' _ q t y) =
      m • WeilValues.isogenyTateWeilPairing A' D' ell' q hdegree' x y := by
  apply PadicInt.ext_of_toZModPow.mp
  intro n
  rw [map_nsmul, WeilValues.isogenyTateWeilPairing_spec, WeilValues.isogenyTateWeilPairing_spec]
  exact isogenyTateWeilResidues_similitude A A' D D' ell ell' q hdegree hdegree' t d hd m hpol n x y

end Similitude

variable {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
  (A : Over (Spec (.of k)))
  [GrpObj A] [IsCommMonObj A] [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
  (D : Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData A)
  (ell : A ⟶ D.abelian) [IsMonHom ell] [IsFinite ell.left] [Flat ell.left] [Surjective ell.left]
  (q : ℕ) [Fact q.Prime]
  (hdegree : ∀ (n : ℕ) (s : Spec (.of k)), (q ^ n).Coprime (ell.left.finrank (η[D.abelian].left s)))
  (t c : A ⟶ A) [IsMonHom t] [IsMonHom c] (d : D.abelian ⟶ D.abelian)
  (hd : d = Picard.Homomorphisms.UnbundledDualPullback.Construction.UnbundledPicard.dualPicardPullback D D t) (hpol : ell ≫ d = c ≫ ell)

include hd hpol in
theorem isogenyTateWeilResidues_adjoint (n : ℕ)
    (x y : Add.schemeTateModule A (Over.mk (𝟙 (Spec (.of k)))) q) :
    WeilValues.isogenyTateWeilResidues A D ell q hdegree n (Add.schemeTateMap A _ q t x) y =
      WeilValues.isogenyTateWeilResidues A D ell q hdegree n x (Add.schemeTateMap A _ q c y) := by
  have he := PolarizationWeilNaturality.geometricIsogenyTorsionPairing_adjoint A D ell (q ^ n)
    (pow_pos (Fact.out : q.Prime).pos n) (hdegree n) t c d hd hpol _
    (WeilValues.nativeTatePoint A _ q n x) (WeilValues.nativeTatePoint A _ q n y)
  rw [← PairingValue.nativeTatePoint_map, ← PairingValue.nativeTatePoint_map] at he
  have hr := PairingValue.tateBicharacterResidues_eq_nsmul_of_values A A q n
    (IsogenyQuotient.Geometric.WeilPairing.Construction.geometricIsogenyTorsionPairing A D ell (q ^ n) (pow_pos (Fact.out : q.Prime).pos n) (hdegree n))
    (IsogenyQuotient.Geometric.WeilPairing.Construction.geometricIsogenyTorsionPairing A D ell (q ^ n) (pow_pos (Fact.out : q.Prime).pos n) (hdegree n))
    (Add.schemeTateMap A _ q t x) y x (Add.schemeTateMap A _ q c y) 1 (by simpa only [pow_one] using he)
  exact hr.trans (one_nsmul _)

include hd hpol in
theorem isogenyTateWeilPairing_adjoint
    (x y : Add.schemeTateModule A (Over.mk (𝟙 (Spec (.of k)))) q) :
    WeilValues.isogenyTateWeilPairing A D ell q hdegree (Add.schemeTateMap A _ q t x) y =
      WeilValues.isogenyTateWeilPairing A D ell q hdegree x (Add.schemeTateMap A _ q c y) := by
  apply PadicInt.ext_of_toZModPow.mp
  intro n
  rw [WeilValues.isogenyTateWeilPairing_spec, WeilValues.isogenyTateWeilPairing_spec]
  exact isogenyTateWeilResidues_adjoint A D ell q hdegree t c d hd hpol n x y

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.WeilNaturality
