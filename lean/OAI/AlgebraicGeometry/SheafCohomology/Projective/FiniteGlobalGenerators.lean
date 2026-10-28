import OAI.AlgebraicGeometry.SheafCohomology.Projective.EpiSectionFamily
import OAI.AlgebraicGeometry.SheafCohomology.Projective.LineBundleSectionCover

/-! # Finite Global Generators -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.FiniteGlobalGenerators

noncomputable section

/-! Finite global generators of actual module sheaves, and their elementary transport operations. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

def HasFiniteGlobalGenerators {X : Scheme.{u}} (M : X.Modules) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (s : ι → (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ M)), Epi (Sigma.desc s)

theorem HasFiniteGlobalGenerators.of_epi {X : Scheme.{u}} {M N : X.Modules}
    (hM : HasFiniteGlobalGenerators M) (f : M ⟶ N) [Epi f] : HasFiniteGlobalGenerators N := by
  obtain ⟨ι, hι, s, hs⟩ := hM
  have := hι
  have := hs
  refine ⟨ι, hι, fun i => s i ≫ f, ?_⟩
  have h : Sigma.desc (fun i => s i ≫ f) = Sigma.desc s ≫ f := by ext; simp
  rw [h]
  infer_instance

theorem HasFiniteGlobalGenerators.of_iso {X : Scheme.{u}} {M N : X.Modules}
    (hM : HasFiniteGlobalGenerators M) (e : M ≅ N) : HasFiniteGlobalGenerators N :=
  hM.of_epi e.hom

theorem HasFiniteGlobalGenerators.pullback {X Y : Scheme.{u}} {M : X.Modules}
    (hM : HasFiniteGlobalGenerators M) (f : Y ⟶ X) :
    HasFiniteGlobalGenerators ((Scheme.Modules.pullback f).obj M) := by
  obtain ⟨ι, hι, s, hs⟩ := hM
  have := hι
  have := hs
  let F := Scheme.Modules.pullback f
  have : Epi (Sigma.desc (fun i => F.map (s i))) :=
    EpiSectionFamily.epi_sigmaDesc_map F (fun _ : ι => AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) s
  refine ⟨ι, hι, fun i => AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection f (s i), ?_⟩
  exact EpiSectionFamily.epi_sigmaDesc_precomp_iso (fun _ : ι => AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y)
    (fun _ : ι => F.obj (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X))
    (fun _ => (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f).symm) (fun i => F.map (s i))

theorem HasFiniteGlobalGenerators.coproduct {X : Scheme.{u}} {ι : Type} [Fintype ι]
    (M : ι → X.Modules) (hM : ∀ i, HasFiniteGlobalGenerators (M i)) :
    HasFiniteGlobalGenerators (∐ M) := by
  classical
  choose κ hκ s hs using hM
  let (i : ι) : Fintype (κ i) := hκ i
  let (i : ι) : Epi (Sigma.desc (s i)) := hs i
  let t : (Σ i, κ i) → (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ ∐ M) := fun i => s i.1 i.2 ≫ Sigma.ι M i.1
  refine ⟨Σ i, κ i, inferInstance, t, ?_⟩
  constructor
  intro Z g h heq
  apply Sigma.hom_ext
  intro i
  apply (cancel_epi (Sigma.desc (s i))).mp
  apply Sigma.hom_ext
  intro j
  have h := congrArg (fun q => Sigma.ι (fun _ : Σ i, κ i => AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) ⟨i, j⟩ ≫ q) heq
  simpa only [Category.assoc, Sigma.ι_comp_desc_assoc, t] using h

theorem HasFiniteGlobalGenerators.section_cover {X : Scheme.{u}} (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X)
    (hL : HasFiniteGlobalGenerators L.sheaf) :
    ∃ (ι : Type) (_ : Fintype ι) (s : ι → (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ L.sheaf)),
      ∀ x : X, ∃ i, x ∈ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (s i) := by
  obtain ⟨ι, hι, s, hs⟩ := hL
  have := hι
  have := hs
  exact ⟨ι, hι, s, LineBundleSectionCover.lineBundle_epi_sections_cover L s⟩

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.FiniteGlobalGenerators
