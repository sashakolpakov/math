import OAI.AlgebraicGeometry.Picard.PoincareBundle.GeneralFieldHomDescent

/-! # Polarization Comparison -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.PolarizationComparison

noncomputable section

/-! Scalar cancellation identifies the global solution with the constructed polarization on each geometric base change. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj BigOperators

open OAI.AlgebraicGeometry.Picard.PoincareBundle.SharedRepresentation

attribute [local instance] Homomorphisms.GroupDescent.Construction.groupHom_pow_isMonHom

/-- The proof fields of an isogeny do not change its identity. -/
theorem isogeny_ext {S : Scheme} {a b : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme a S} {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme b S}
    (p q : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B) (h : p.hom = q.hom) : p = q := by
  cases p
  cases q
  cases h
  rfl

variable {k : Type} [Field k] {a : ℕ} {A B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme a (Spec (.of k))}
  (DA : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (DB : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData B) {δ : Fin a → ℕ}
  (pol : AbelianModuli.HilbertConstruction.PolarizationData.Polarization DA δ) (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B)

/-- The descended isogeny is the positive polarization of unchanged type on every algebraically closed field extension. -/
theorem exists_polarization_eq (n : ℕ) (hn : 0 < n) (hnd : n.Coprime ((∏ i, δ i) ^ 2))
    (hf : ∀ (T : Over (Spec (.of k))) (x : T ⟶ A.scheme), x ≫ f.hom = 1 → x ^ n = 1)
    (hlag : WeilIsotropy.SelfAnnihilating DA pol f n hn hf)
    (m : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny B DB.abelian)
    (hm : f.hom ≫ m.hom ≫ DualMaps.representedDualMap
      (SharedRepresentation.representation (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled DA)) (SharedRepresentation.representation (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled DB)) f.hom = pol.isogeny.hom ^ n)
    (K : Type) [Field K] [IsAlgClosed K] (s : Spec (.of K) ⟶ Spec (.of k)) :
    ∃ r : AbelianModuli.HilbertConstruction.PolarizationData.Polarization (DB.pullback s) δ, m.pullback s = r.isogeny := by
  let F := Over.pullback s
  have : EffectiveEpi (f.pullback s).hom := EffectiveOverQuotient.affine_effective (f.pullback s).hom
  have : EffectiveEpi ((𝟙 (B.pullback s).scheme) ^ n) :=
    PoincareBundle.Field.QuotientScalarCovers.effective (DA.pullback s) (pol.pullback s).isogeny (f.pullback s) n hn
  obtain ⟨_, e, _, _, _, hde⟩ := PoincareBundle.Field.DualComplement.exists_complements DA DB f n hf
  let d : DB.abelian.scheme ⟶ DA.abelian.scheme := DualMaps.representedDualMap (SharedRepresentation.representation (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled DA))
    (SharedRepresentation.representation (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled DB)) f.hom
  have hde' : F.map d ≫ F.map e = (𝟙 (DB.abelian.pullback s).scheme) ^ n :=
    (F.map_comp d e).symm.trans ((congrArg F.map hde).trans
      (MonoidalScalarPreservation.map_scalar F DB.abelian.scheme n))
  obtain ⟨r, hr, _⟩ := WeilIsotropy.existsUnique_on_field DA pol f n hn hf DB hnd hlag K s
  have : IsMonHom (show (B.pullback s).scheme ⟶ F.obj DB.abelian.scheme from (m.pullback s).hom) :=
    (m.pullback s).preservesGroup
  have : IsMonHom (show (B.pullback s).scheme ⟶ F.obj DB.abelian.scheme from r.isogeny.hom) :=
    r.isogeny.preservesGroup
  have hm' : F.map f.hom ≫ (m.pullback s).hom ≫ F.map d = (F.map pol.isogeny.hom) ^ n := by
    exact ((congrArg (fun t => F.map f.hom ≫ t) (F.map_comp m.hom d).symm).trans
      ((F.map_comp f.hom (m.hom ≫ d)).symm.trans (congrArg F.map hm))).trans
        (MonoidalScalarPreservation.map_pow F pol.isogeny.hom n)
  refine ⟨r, isogeny_ext _ _ ?_⟩
  exact Scalar.PullbackCancellation.pullback_injective (f.pullback s).hom (F.map d) (F.map e) n hde'
    (m.pullback s).hom r.isogeny.hom (hm'.trans hr.symm)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.PolarizationComparison
