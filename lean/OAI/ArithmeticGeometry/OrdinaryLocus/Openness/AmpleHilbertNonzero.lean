import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ProperSectionFiniteness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ZeroSections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.Sections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.PowerLocus

/-! # Ample Hilbert Nonzero -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.AmpleHilbertNonzero.Construction

noncomputable section

/-! The actual Hilbert polynomial of an ample line bundle on a nonempty proper scheme is nonzero. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem lineBundle_section_value_ne_zero
    {X : Scheme} (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (s : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ L.sheaf)
    (x : X) (hx : x ∈ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s) :
    AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv L.sheaf s ≠ 0 := by
  intro hz
  have hs : s = 0 := (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv L.sheaf).injective (by
    change s.app ⊤ (1 : Γ(X, ⊤)) = 0
    exact hz)
  rw [hs, L.sectionNonvanishing_zero] at hx
  exact hx.elim

theorem ampleHilbertPolynomial_ne_zero
    {X S : Scheme.{0}} [Nonempty X] [IsAffine S]
    (f : X ⟶ S) [IsProper f] (hfield : IsField Γ(S, ⊤))
    (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (hL : L.IsAmple) (d : ℕ) (_hd : 0 < d)
    (P : Polynomial ℚ) (b : ℕ)
    (hP : ∀ n : ℕ, b ≤ n →
      (Module.finrank Γ(S, ⊤) ((AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor f).obj
        (L.tensorPower (n * d)).sheaf) : ℚ) = P.eval (n : ℚ)) : P ≠ 0 := by
  let : Field Γ(S, ⊤) := hfield.toField
  have : CompactSpace X := ⟨hL.1⟩
  have : X.IsSeparated := ⟨(Limits.terminal.comp_from f) ▸
    (inferInstance : IsSeparated (f ≫ Limits.terminal.from S))⟩
  obtain ⟨a, ha, r, s, hs, _⟩ := hL.projective_section_family
  let x : X := Classical.choice inferInstance
  obtain ⟨i, hi⟩ := hs x
  let n := (b + 1) * a
  let t := AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.Maps.tensorPowerSection (s i) ((b + 1) * d)
  let T := (L.tensorPower a).tensorPower ((b + 1) * d)
  have ht : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv T.sheaf t ≠ 0 :=
    lineBundle_section_value_ne_zero T t x
      (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Power.Nonvanishing.sectionNonvanishing_le_tensorPowerSection (s i) ((b + 1) * d) hi)
  have he : ((b + 1) * d) * a = n * d := by dsimp [n]; ac_rfl
  let e : T.sheaf ≅ (L.tensorPower (n * d)).sheaf :=
    (L.tensorPowerComposeIso ((b + 1) * d) a).symm ≪≫
      eqToIso (congrArg (fun k => (L.tensorPower k).sheaf) he)
  let eV := ((AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor f).mapIso e).toLinearEquiv
  have : Nontrivial ((AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor f).obj (L.tensorPower (n * d)).sheaf) :=
    ⟨⟨eV (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv T.sheaf t), 0,
      fun h => ht (eV.injective (h.trans eV.map_zero.symm))⟩⟩
  have : (L.tensorPower (n * d)).sheaf.IsQuasicoherent :=
    LineBundleQuasicoherent.Construction.isQuasicoherent_of_isLineBundle _ (L.tensorPower (n * d)).locallyTrivial
  have : (L.tensorPower (n * d)).sheaf.IsFiniteType :=
    ProjectiveCohomologyFiniteness.Construction.isFiniteType_of_isLineBundle _ (L.tensorPower (n * d)).locallyTrivial
  have : Module.Finite Γ(S, ⊤) ((AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor f).obj
      (L.tensorPower (n * d)).sheaf) :=
    ProperSectionFiniteness.Construction.ample_proper_globalSections_finite f L hL _
  have hp : 0 < Module.finrank Γ(S, ⊤) ((AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor f).obj
      (L.tensorPower (n * d)).sheaf) := Module.finrank_pos
  have hn : b ≤ n := (Nat.le_succ b).trans (Nat.le_mul_of_pos_right (b + 1) ha)
  intro hz
  have h := hP n hn
  rw [hz, Polynomial.eval_zero] at h
  exact hp.ne' (Nat.cast_eq_zero.mp h)

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.AmpleHilbertNonzero.Construction
