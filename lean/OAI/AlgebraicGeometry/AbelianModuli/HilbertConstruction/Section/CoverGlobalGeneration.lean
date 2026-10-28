import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.GlobalModuleGenerators
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.EpimorphismCover
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.Frames
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Power.ProjectiveEmbeddings

/-! # Cover Global Generation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Actual nonvanishing section covers give epimorphic section families, including every positive tensor power and every retained projective embedding power. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

theorem Section.CoverGlobalGeneration.sectionFamily_epi_of_nonvanishing_cover
    {X : Scheme.{u}} {ι : Type u} {M : X.Modules}
    (s : ι → (Line.Bundles.structureModule X ⟶ M))
    (hs : ∀ x : X, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (s i)) : Epi (Sigma.desc s) := by
  apply Module.EpimorphismCover.module_epi_of_restrict_cover (fun i => Ample.LineBundles.sectionNonvanishing (s i)) hs
  intro i
  let F := Scheme.Modules.restrictFunctor (Ample.LineBundles.sectionNonvanishing (s i)).ι
  have : IsIso (F.map (s i)) :=
    (Power.Nonvanishing.isIso_restrict_map_iff (Ample.LineBundles.sectionNonvanishing (s i)).ι (s i)).mpr
      ((Section.Nonvanishing.isIso_pullbackSection_iff (Ample.LineBundles.sectionNonvanishing (s i)).ι (s i)).mp inferInstance)
  constructor
  intro Z g h he
  change F.map (Sigma.desc s) ≫ g = F.map (Sigma.desc s) ≫ h at he
  apply (cancel_epi (F.map (s i))).mp
  have he' := congrArg (fun q => F.map (Sigma.ι (fun _ : ι => Line.Bundles.structureModule X) i) ≫ q) he
  simpa only [← Category.assoc, ← CategoryTheory.Functor.map_comp, Sigma.ι_comp_desc] using he'

theorem Finite.GlobalModuleGenerators.HasFiniteGlobalGenerators.of_section_cover
    {X : Scheme.{u}} {ι : Type u} [Finite ι] {M : X.Modules}
    (s : ι → (Line.Bundles.structureModule X ⟶ M))
    (hs : ∀ x : X, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (s i)) : HilbertConstruction.Finite.GlobalModuleGenerators.HasFiniteGlobalGenerators M :=
  ⟨ι, inferInstance, s, Section.CoverGlobalGeneration.sectionFamily_epi_of_nonvanishing_cover s hs⟩

theorem Section.CoverGlobalGeneration.lineBundle_tensorPower_finiteGlobalGenerators_of_cover
    {X : Scheme.{u}} {ι : Type u} [Finite ι] (L : Line.Bundles.LineBundle X)
    (s : ι → (Line.Bundles.structureModule X ⟶ L.sheaf))
    (hs : ∀ x : X, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (s i)) (d : ℕ) (hd : 0 < d) :
    HilbertConstruction.Finite.GlobalModuleGenerators.HasFiniteGlobalGenerators (L.tensorPower d).sheaf := by
  apply HilbertConstruction.Finite.GlobalModuleGenerators.HasFiniteGlobalGenerators.of_section_cover (fun i => TensorPower.Maps.tensorPowerSection (s i) d)
  intro x
  obtain ⟨i, hi⟩ := hs x
  exact ⟨i, (Section.PowerLocus.sectionNonvanishing_tensorPowerSection (s i) d hd).symm ▸ hi⟩

theorem Power.ProjectiveEmbeddings.PowerProjectiveEmbedding.power_hasFiniteGlobalGenerators
    {X S : Scheme.{u}} {L : Line.Bundles.LineBundle X} {f : X ⟶ S} (E : Power.ProjectiveEmbeddings.PowerProjectiveEmbedding L f) :
    HilbertConstruction.Finite.GlobalModuleGenerators.HasFiniteGlobalGenerators E.power.sheaf := by
  let s : ULift.{u} (Fin (E.dimension + 1)) → (Line.Bundles.structureModule X ⟶ E.power.sheaf) :=
    fun i => E.sections i.down
  apply HilbertConstruction.Finite.GlobalModuleGenerators.HasFiniteGlobalGenerators.of_section_cover s
  intro x
  obtain ⟨i, hi⟩ := E.covers x
  exact ⟨⟨i⟩, hi⟩

theorem Power.ProjectiveEmbeddings.PowerProjectiveEmbedding.degreePower_hasFiniteGlobalGenerators
    {X S : Scheme.{u}} {L : Line.Bundles.LineBundle X} {f : X ⟶ S} (E : Power.ProjectiveEmbeddings.PowerProjectiveEmbedding L f) :
    HilbertConstruction.Finite.GlobalModuleGenerators.HasFiniteGlobalGenerators (L.tensorPower E.degree).sheaf :=
  E.power_hasFiniteGlobalGenerators.of_iso
    (E.isPower.unique (L.tensorPower_isTensorPower E.degree)).some

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
