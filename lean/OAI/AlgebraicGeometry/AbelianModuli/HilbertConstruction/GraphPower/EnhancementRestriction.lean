import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphPower.EnhancementFamilyTransport
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphPower.EnhancementNormalization
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.RecoveryComposition
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.Comparisons

/-! # Enhancement Restriction -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphPower.EnhancementRestriction

noncomputable section

/-! Existence of the original graph-power enhancement is invariant under
the canonical comparison between a single and an iterated base change.
The normalized form matches the affine rational-polarization parameters. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

theorem graphPowerEnhancement_nonempty_iff_of_groupIso
    {S : Scheme.{u}} {g N : ℕ} (δ : Fin g → ℕ)
    (F G : Level.Data.AbelianSchemeWithFullLevel g N S)
    (L : Line.Bundles.LineBundle F.abelian.scheme.left) (M : Line.Bundles.LineBundle G.abelian.scheme.left) (d : ℕ)
    (e : F.abelian.scheme ≅ G.abelian.scheme) [IsMonHom e.hom]
    (he : Line.Bundles.LineBundle.pullbackClass e.hom.left (Line.Bundles.LineBundle.classOf M) = Line.Bundles.LineBundle.classOf L) :
    Nonempty (PolarizationEnhancementData.GraphPowerPolarizationEnhancement δ F L d) ↔
      Nonempty (PolarizationEnhancementData.GraphPowerPolarizationEnhancement δ G M d) := by
  constructor
  · rintro ⟨H⟩
    exact ⟨H.transportFamily (G := G) e he⟩
  · rintro ⟨H⟩
    let : IsMonHom e.symm.hom := inferInstanceAs (IsMonHom e.inv)
    exact ⟨H.transportFamily (G := F) e.symm (Line.Bundles.LineBundle.inverseRecovery e L M he)⟩

theorem graphPowerEnhancement_nonempty_iff_of_bundleIso
    {S : Scheme.{u}} {g N : ℕ} (δ : Fin g → ℕ)
    (F : Level.Data.AbelianSchemeWithFullLevel g N S)
    (L M : Line.Bundles.LineBundle F.abelian.scheme.left) (d : ℕ) (e : L.sheaf ≅ M.sheaf) :
    Nonempty (PolarizationEnhancementData.GraphPowerPolarizationEnhancement δ F L d) ↔
      Nonempty (PolarizationEnhancementData.GraphPowerPolarizationEnhancement δ F M d) := by
  constructor
  · rintro ⟨H⟩
    exact ⟨H.ofBundleIso e.symm⟩
  · rintro ⟨H⟩
    exact ⟨H.ofBundleIso e⟩

theorem graphPowerEnhancement_baseChange_comp_iff
    {S U T : Scheme.{u}} {g N : ℕ} (δ : Fin g → ℕ)
    (F : Level.Data.AbelianSchemeWithFullLevel g N S)
    (L : Line.Bundles.LineBundle F.abelian.scheme.left) (d : ℕ) (i : U ⟶ S) (t : T ⟶ U) :
    Nonempty (PolarizationEnhancementData.GraphPowerPolarizationEnhancement δ (F.pullback (t ≫ i))
      (L.pullback (pullback.fst F.abelian.scheme.hom (t ≫ i))) d) ↔
    Nonempty (PolarizationEnhancementData.GraphPowerPolarizationEnhancement δ ((F.pullback i).pullback t)
      ((L.pullback (pullback.fst F.abelian.scheme.hom i)).pullback
        (pullback.fst (F.abelian.pullback i).scheme.hom t)) d) := by
  let G := (F.pullback i).pullback t
  let H := F.pullback (t ≫ i)
  let e : G.abelian.scheme ≅ H.abelian.scheme := (F.abelian.pullbackCompIso i t).symm
  let : IsMonHom e.hom := inferInstanceAs (IsMonHom (F.abelian.pullbackCompIso i t).inv)
  let a := pullback.fst F.abelian.scheme.hom (t ≫ i)
  let b := pullback.fst F.abelian.scheme.hom i
  let c := pullback.fst (F.abelian.pullback i).scheme.hom t
  have hp : e.hom.left ≫ a = c ≫ b := F.abelian.pullbackCompIso_inv_left_fst i t
  have he : Line.Bundles.LineBundle.pullbackClass e.hom.left (Line.Bundles.LineBundle.classOf (L.pullback a)) =
      Line.Bundles.LineBundle.classOf ((L.pullback b).pullback c) :=
    (Line.Bundles.LineBundle.pullbackClass_comp e.hom.left a (Line.Bundles.LineBundle.classOf L)).symm.trans
      ((congrArg (fun f => Line.Bundles.LineBundle.pullbackClass f (Line.Bundles.LineBundle.classOf L)) hp).trans
        (Line.Bundles.LineBundle.pullbackClass_comp c b (Line.Bundles.LineBundle.classOf L)))
  exact (graphPowerEnhancement_nonempty_iff_of_groupIso δ G H
    ((L.pullback b).pullback c) (L.pullback a) d e he).symm

theorem normalizedGraphPowerEnhancement_baseChange_comp_iff
    {S U T : Scheme.{u}} {g N : ℕ} (δ : Fin g → ℕ)
    (F : Level.Data.AbelianSchemeWithFullLevel g N S)
    (L : Line.Bundles.LineBundle F.abelian.scheme.left) (d : ℕ) (i : U ⟶ S) (t : T ⟶ U) :
    Nonempty (PolarizationEnhancementData.GraphPowerPolarizationEnhancement δ (F.pullback (t ≫ i))
      ((F.abelian.zeroNormalizedBundle L).pullback
        (pullback.fst F.abelian.scheme.hom (t ≫ i))) d) ↔
    Nonempty (PolarizationEnhancementData.GraphPowerPolarizationEnhancement δ ((F.pullback i).pullback t)
      (((F.abelian.pullback i).zeroNormalizedBundle
        (L.pullback (pullback.fst F.abelian.scheme.hom i))).pullback
          (pullback.fst (F.abelian.pullback i).scheme.hom t)) d) := by
  let e := (Scheme.Modules.pullback (pullback.fst (F.abelian.pullback i).scheme.hom t)).mapIso
    (F.abelian.zeroNormalizedBundle_baseChangeIso L i)
  exact (graphPowerEnhancement_baseChange_comp_iff δ F (F.abelian.zeroNormalizedBundle L) d i t).trans
    (graphPowerEnhancement_nonempty_iff_of_bundleIso δ ((F.pullback i).pullback t) _ _ d e)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphPower.EnhancementRestriction
