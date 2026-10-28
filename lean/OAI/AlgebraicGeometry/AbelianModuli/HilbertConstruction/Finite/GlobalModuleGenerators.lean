import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.EpimorphicCoproductFamilies
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles

/-! # Global Module Generators -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.GlobalModuleGenerators

noncomputable section

/-! Finite global generation is witnessed by actual section maps with epimorphic coproduct. These witnesses descend through epimorphisms and survive pullback and finite coproducts. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

def HasFiniteGlobalGenerators {X : Scheme.{u}} (M : X.Modules) : Prop :=
  ∃ (ι : Type u) (_ : Finite ι) (s : ι → (Line.Bundles.structureModule X ⟶ M)), Epi (Sigma.desc s)

theorem HasFiniteGlobalGenerators.of_epi {X : Scheme.{u}} {M N : X.Modules}
    (hM : HasFiniteGlobalGenerators M) (f : M ⟶ N) [Epi f] : HasFiniteGlobalGenerators N := by
  obtain ⟨ι, hι, s, hs⟩ := hM
  have := hι
  have := hs
  refine ⟨ι, hι, fun i => s i ≫ f, ?_⟩
  have h : Sigma.desc (fun i => s i ≫ f) = Sigma.desc s ≫ f := by
    ext i
    simp
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
    EpimorphicCoproductFamilies.epi_sigmaDesc_map F (fun _ : ι => Line.Bundles.structureModule X) s
  refine ⟨ι, hι, fun i => Ample.LineBundles.pullbackSection f (s i), ?_⟩
  exact EpimorphicCoproductFamilies.epi_sigmaDesc_precomp_iso (fun _ : ι => Line.Bundles.structureModule Y)
    (fun _ : ι => F.obj (Line.Bundles.structureModule X))
    (fun _ => (Line.Bundles.structureModulePullbackIso f).symm) (fun i => F.map (s i))

theorem HasFiniteGlobalGenerators.coproduct {X : Scheme.{u}} {ι : Type u} [Finite ι]
    (M : ι → X.Modules) (hM : ∀ i, HasFiniteGlobalGenerators (M i)) :
    HasFiniteGlobalGenerators (∐ M) := by
  classical
  choose κ hκ s hs using hM
  let (i : ι) : Finite (κ i) := hκ i
  let (i : ι) : Epi (Sigma.desc (s i)) := hs i
  let t : (Σ i, κ i) → (Line.Bundles.structureModule X ⟶ ∐ M) := fun i => s i.1 i.2 ≫ Sigma.ι M i.1
  refine ⟨Σ i, κ i, inferInstance, t, ?_⟩
  constructor
  intro Z g h heq
  apply Sigma.hom_ext
  intro i
  apply (cancel_epi (Sigma.desc (s i))).mp
  apply Sigma.hom_ext
  intro j
  have he := congrArg (fun q => Sigma.ι (fun _ : Σ i, κ i => Line.Bundles.structureModule X) ⟨i, j⟩ ≫ q) heq
  simpa only [Category.assoc, Sigma.ι_comp_desc_assoc, t] using he

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.GlobalModuleGenerators
