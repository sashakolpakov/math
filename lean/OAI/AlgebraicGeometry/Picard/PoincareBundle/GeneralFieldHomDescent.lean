import OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.WeilIsotropy
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Field.DualComplement
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Field.QuotientScalarCovers
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Scalar.FactorDescent
import OAI.AlgebraicGeometry.Picard.PoincareBundle.DescendedIsogeny
import OAI.AlgebraicGeometry.Picard.PoincareBundle.PositiveMultiple

/-! # General Field Hom Descent -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.Picard.PoincareBundle.GeneralFieldHomDescent

/-! Faithful algebraic closure and effective scalar quotients construct the unique descended homomorphism over the original field. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj BigOperators

open OAI.AlgebraicGeometry.Picard.PoincareBundle.SharedRepresentation

attribute [local instance] Homomorphisms.GroupDescent.Construction.groupHom_pow_isMonHom

variable {k : Type} [Field k] {a : ℕ} {A B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme a (Spec (.of k))}
  (DA : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (DB : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData B) {δ : Fin a → ℕ}
  (pol : AbelianModuli.HilbertConstruction.PolarizationData.Polarization DA δ) (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B)

/-- The two-sided polarization equation has exactly one group homomorphism solution over an arbitrary field. -/
theorem existsUnique_homomorphism (n : ℕ) (hn : 0 < n) (hnd : n.Coprime ((∏ i, δ i) ^ 2))
    (hf : ∀ (T : Over (Spec (.of k))) (x : T ⟶ A.scheme), x ≫ f.hom = 1 → x ^ n = 1)
    (hlag : Geometric.WeilIsotropy.SelfAnnihilating DA pol f n hn hf) :
    ∃! m : B.scheme ⟶ DB.abelian.scheme, IsMonHom m ∧
      f.hom ≫ m ≫ DualMaps.representedDualMap
        (SharedRepresentation.representation (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled DA)) (SharedRepresentation.representation (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled DB)) f.hom =
          pol.isogeny.hom ^ n := by
  let s := Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))
  let F := Over.pullback s
  have : F.Faithful := PoincareBundle.Field.Extension.pullback_faithful s
  have : EffectiveEpi f.hom := EffectiveOverQuotient.affine_effective f.hom
  have : EffectiveEpi ((𝟙 B.scheme) ^ n) := PoincareBundle.Field.QuotientScalarCovers.effective DA pol.isogeny f n hn
  have : EffectiveEpi ((𝟙 B.scheme) ^ (n * n)) :=
    PoincareBundle.Field.QuotientScalarCovers.effective DA pol.isogeny f (n * n) (Nat.mul_pos hn hn)
  have hlocal : EffectiveEpi ((𝟙 (B.pullback s).scheme) ^ (n * n)) :=
    PoincareBundle.Field.QuotientScalarCovers.effective (DA.pullback s) (pol.pullback s).isogeny (f.pullback s)
      (n * n) (Nat.mul_pos hn hn)
  have : EffectiveEpi (F.map ((𝟙 B.scheme) ^ (n * n))) :=
    (MonoidalScalarPreservation.map_scalar F B.scheme (n * n)).symm ▸ hlocal
  obtain ⟨g, e, _, _, hgf, hde⟩ := PoincareBundle.Field.DualComplement.exists_complements DA DB f n hf
  obtain ⟨m, hm, _⟩ := Geometric.WeilIsotropy.existsUnique_on_field DA pol f n hn hf DB hnd hlag
    (AlgebraicClosure k) s
  have : IsMonHom (show F.obj B.scheme ⟶ F.obj DB.abelian.scheme from m.isogeny.hom) := m.isogeny.preservesGroup
  have hm' : F.map f.hom ≫ m.isogeny.hom ≫ F.map (DualMaps.representedDualMap
      (SharedRepresentation.representation (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled DA)) (SharedRepresentation.representation (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled DB)) f.hom) =
        F.map (pol.isogeny.hom ^ n) :=
    hm.trans (MonoidalScalarPreservation.map_pow F pol.isogeny.hom n).symm
  exact Scalar.FactorDescent.existsUnique_homomorphism F f.hom g _ e _ n hgf hde m.isogeny.hom hm'

end AlgebraicGeometry.Picard.PoincareBundle.GeneralFieldHomDescent

namespace AlgebraicGeometry.Picard.PoincareBundle.GeneralFieldHomDescent.Isogeny

/-! The descended homomorphism has actual finite, flat, and surjective scheme geometry over the original field. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj BigOperators

open OAI.AlgebraicGeometry.Picard.PoincareBundle.SharedRepresentation

attribute [local instance] Homomorphisms.GroupDescent.Construction.groupHom_pow_isMonHom

variable {k : Type} [Field k] {a : ℕ} {A B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme a (Spec (.of k))}
  (DA : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (DB : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData B) {δ : Fin a → ℕ}
  (pol : AbelianModuli.HilbertConstruction.PolarizationData.Polarization DA δ) (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B)

/-- No geometric isogeny property is assumed of the descended map: its scalar complements prove all three properties. -/
theorem existsUnique_isogeny (n : ℕ) (hn : 0 < n) (hnd : n.Coprime ((∏ i, δ i) ^ 2))
    (hf : ∀ (T : Over (Spec (.of k))) (x : T ⟶ A.scheme), x ≫ f.hom = 1 → x ^ n = 1)
    (hlag : Geometric.WeilIsotropy.SelfAnnihilating DA pol f n hn hf) :
    ∃! m : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny B DB.abelian,
      f.hom ≫ m.hom ≫ DualMaps.representedDualMap
        (SharedRepresentation.representation (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled DA)) (SharedRepresentation.representation (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled DB)) f.hom =
          pol.isogeny.hom ^ n := by
  obtain ⟨m, hm, hu⟩ := existsUnique_homomorphism DA DB pol f n hn hnd hf hlag
  have : IsMonHom m := hm.1
  have : IsMonHom (show B.scheme ⟶ (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled DB).abelian from m) := hm.1
  have : IsMonHom (show A.scheme ⟶ (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled DA).abelian from pol.isogeny.hom) := pol.isogeny.preservesGroup
  have : IsFinite (show A.scheme ⟶ (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled DA).abelian from pol.isogeny.hom).left := pol.isogeny.finite
  have : Flat (show A.scheme ⟶ (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled DA).abelian from pol.isogeny.hom).left := pol.isogeny.flat
  have : Surjective (show A.scheme ⟶ (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled DA).abelian from pol.isogeny.hom).left := pol.isogeny.surjective
  obtain ⟨hfin, hflat, hsurj⟩ := PositiveMultiple.positive_multiple_cover (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled DA) pol.isogeny.hom n hn
  have : IsFinite (pol.isogeny.hom ^ n).left := hfin
  have : Flat (pol.isogeny.hom ^ n).left := hflat
  have : Surjective (pol.isogeny.hom ^ n).left := hsurj
  let d : (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled DB).abelian ⟶ DA.abelian.scheme := DualMaps.representedDualMap (SharedRepresentation.representation (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled DA))
    (SharedRepresentation.representation (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled DB)) f.hom
  have : IsMonHom d := PoincareBundle.Field.DualGroupHom.isMonHom f.hom DA DB
  obtain ⟨_, e, _, _, _, hde⟩ := PoincareBundle.Field.DualComplement.exists_complements DA DB f n hf
  obtain ⟨hmfin, hmflat, hmsurj⟩ := DescendedIsogeny.finite_flat_surjective
    (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled DB) f.hom m d (pol.isogeny.hom ^ n) hm.2 e n hn hde
  let r : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny B DB.abelian := ⟨m, hm.1, hmfin, hmflat, hmsurj⟩
  refine ⟨r, hm.2, ?_⟩
  intro t ht
  have heq : t.hom = r.hom := hu t.hom ⟨t.preservesGroup, ht⟩
  cases t
  cases heq
  rfl

end AlgebraicGeometry.Picard.PoincareBundle.GeneralFieldHomDescent.Isogeny

end

end OAI
