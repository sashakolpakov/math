import OAI.AlgebraicGeometry.PELModuli.CMPoints.TorsionFactorIso
import OAI.AlgebraicGeometry.PELModuli.CMPoints.BlockRetraction
import OAI.AlgebraicGeometry.CartierDuality.PolarizedTorsion

/-! # Polarized Torsion Finiteness -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.PolarizedTorsionFiniteness

noncomputable section

section

/-! Finite locally free torsion for the polarized family and for its
actual scalar factors away from the scalar multiplier. This includes
torsion in the residue characteristic. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.CartierDuality.PolarizedTorsion.Construction

variable {S : Scheme.{0}} {g h : ℕ}

theorem polarized_multiplication_finite_flat {δ : Fin g → ℕ} {N : ℕ}
    (P : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S) (m : ℕ) (hm : 0 < m) :
    IsFinite (P.abelian.multiplication m).left ∧ Flat (P.abelian.multiplication m).left ∧
      LocallyOfFinitePresentation (P.abelian.multiplication m).left := by
  let D := Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled P.dual
  have : IsMonHom (show P.abelian.scheme ⟶ D.abelian from P.polarization.isogeny.hom) :=
    P.polarization.isogeny.preservesGroup
  have : IsFinite (show P.abelian.scheme ⟶ D.abelian from P.polarization.isogeny.hom).left :=
    P.polarization.isogeny.finite
  have hc := AbelianScheme.CartierDuality.MultiplicationCovers.Construction.RelativeAbelian.positive_power_cover P.abelian.scheme D
    P.polarization.isogeny.hom m hm
  exact ⟨hc.1, hc.2.1, hc.2.2.2⟩

theorem polarized_torsion_finite_flat {δ : Fin g → ℕ} {N : ℕ}
    (P : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S) (m : ℕ) (hm : 0 < m) :
    IsFinite (P.abelian.torsionScheme m).hom ∧ Flat (P.abelian.torsionScheme m).hom ∧
      LocallyOfFinitePresentation (P.abelian.torsionScheme m).hom := by
  obtain ⟨hf, hflat, hfp⟩ := polarized_multiplication_finite_flat P m hm
  let : IsFinite (P.abelian.multiplication m).left := hf
  let : Flat (P.abelian.multiplication m).left := hflat
  let : LocallyOfFinitePresentation (P.abelian.multiplication m).left := hfp
  exact ⟨inferInstanceAs (IsFinite (CategoryTheory.Limits.pullback.snd
      (P.abelian.multiplication m).left η[P.abelian.scheme].left)),
    inferInstanceAs (Flat (CategoryTheory.Limits.pullback.snd
      (P.abelian.multiplication m).left η[P.abelian.scheme].left)),
    inferInstanceAs (LocallyOfFinitePresentation (CategoryTheory.Limits.pullback.snd
      (P.abelian.multiplication m).left η[P.abelian.scheme].left))⟩

theorem torsion_finite_flat_of_functor_retract
    (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h S) (m : ℕ)
    [IsFinite (A.torsionScheme m).hom] [Flat (A.torsionScheme m).hom]
    [LocallyOfFinitePresentation (A.torsionScheme m).hom]
    (i : B.torsionFunctor m ⟶ A.torsionFunctor m)
    (r : A.torsionFunctor m ⟶ B.torsionFunctor m) (hir : i ≫ r = 𝟙 _) :
    IsFinite (B.torsionScheme m).hom ∧ Flat (B.torsionScheme m).hom ∧
      LocallyOfFinitePresentation (B.torsionScheme m).hom := by
  let i' : Grp.mk (B.torsionScheme m) ⟶ Grp.mk (A.torsionScheme m) :=
    yonedaGrpFullyFaithful.preimage
      ((B.torsionSchemeYonedaIso m).hom ≫ i ≫ (A.torsionSchemeYonedaIso m).inv)
  let r' : Grp.mk (A.torsionScheme m) ⟶ Grp.mk (B.torsionScheme m) :=
    yonedaGrpFullyFaithful.preimage
      ((A.torsionSchemeYonedaIso m).hom ≫ r ≫ (B.torsionSchemeYonedaIso m).inv)
  have h' : i' ≫ r' = 𝟙 _ := by
    apply yonedaGrp.map_injective
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id]
    dsimp only [i', r']
    rw [yonedaGrpFullyFaithful.map_preimage, yonedaGrpFullyFaithful.map_preimage]
    exact BlockRetraction.iso_conjugated_retraction (B.torsionSchemeYonedaIso m)
      (A.torsionSchemeYonedaIso m) i r hir
  exact AbelianScheme.CartierDuality.IntrinsicRetracts.Construction.Schemes.finiteLocallyFree_of_retract i' r' h'

def piGroupProjection {C : Type*} [Category* C] {I : Type} [Fintype I]
    (F : I → C ⥤ CommGrpCat) (i : I) :
    FlattenTorsionFactors.piGroupFunctor F ⟶ F i ⋙ forget₂ CommGrpCat GrpCat where
  app T := GrpCat.ofHom (Pi.evalMonoidHom (fun j => (F j).obj T) i)
  naturality _ _ _ := rfl

theorem piGroupInclusion_projection {C : Type*} [Category* C] {I : Type} [Fintype I]
    (F : I → C ⥤ CommGrpCat) (i : I) :
    FlattenTorsionFactors.piGroupInclusion F i ≫ piGroupProjection F i = 𝟙 _ := by
  apply NatTrans.ext
  funext T
  apply GrpCat.hom_ext
  apply MonoidHom.ext
  intro x
  change (Pi.mulSingle i x : ∀ j, (F j).obj T) i = x
  simp

theorem scalar_factor_torsion_finite_flat {I : Type} [Fintype I] {d : I → ℕ}
    {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S} {B : ∀ i, AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme (d i) S}
    (D : TorsionFactorIso.AbelianScalarFactorization A B) (m : ℕ) (hm : m.Coprime D.multiplier)
    [IsFinite (A.torsionScheme m).hom] [Flat (A.torsionScheme m).hom]
    [LocallyOfFinitePresentation (A.torsionScheme m).hom] (i : I) :
    IsFinite ((B i).torsionScheme m).hom ∧ Flat ((B i).torsionScheme m).hom ∧
      LocallyOfFinitePresentation ((B i).torsionScheme m).hom := by
  let e := D.torsionFactorIso m hm
  let inc := FlattenTorsionFactors.piGroupInclusion (fun i => TorsionFactorIso.torsionCommFunctor (B i) m) i
  let proj := piGroupProjection (fun i => TorsionFactorIso.torsionCommFunctor (B i) m) i
  apply torsion_finite_flat_of_functor_retract A (B i) m (inc ≫ e.inv) (e.hom ≫ proj)
  exact (Category.assoc inc e.inv (e.hom ≫ proj)).trans
    ((congrArg (fun t => inc ≫ t) (e.inv_hom_id_assoc proj)).trans
      (piGroupInclusion_projection _ i))

end

/-! Concrete finite flat torsion at a fixed prime, derived from the
supplied polarization and the actual scalar factorization. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {S : Scheme.{0}} {g : ℕ}

def TorsionFiniteLocallyFree (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (q : ℕ) : Prop :=
  ∀ n : ℕ, IsFinite (A.torsionScheme (q ^ n)).hom ∧ Flat (A.torsionScheme (q ^ n)).hom ∧
    LocallyOfFinitePresentation (A.torsionScheme (q ^ n)).hom

theorem polarized_torsion_finite_locally_free {δ : Fin g → ℕ} {N q : ℕ}
    (P : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S) (hq : 0 < q) :
    TorsionFiniteLocallyFree P.abelian q :=
  fun n => polarized_torsion_finite_flat P (q ^ n) (pow_pos hq n)

theorem scalar_factor_torsion_finite_locally_free {I : Type} [Fintype I] {d : I → ℕ}
    {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S} {B : ∀ i, AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme (d i) S}
    (D : TorsionFactorIso.AbelianScalarFactorization A B) {q : ℕ}
    (hA : TorsionFiniteLocallyFree A q) (hq : q.Coprime D.multiplier) (i : I) :
    TorsionFiniteLocallyFree (B i) q := by
  intro n
  obtain ⟨hf, hflat, hfp⟩ := hA n
  let : IsFinite (A.torsionScheme (q ^ n)).hom := hf
  let : Flat (A.torsionScheme (q ^ n)).hom := hflat
  let : LocallyOfFinitePresentation (A.torsionScheme (q ^ n)).hom := hfp
  exact scalar_factor_torsion_finite_flat D (q ^ n) (hq.pow_left n) i

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.PolarizedTorsionFiniteness
