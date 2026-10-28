import OAI.RepresentationTheory.Theta.Geometric.FppfPicardLocality
import Mathlib.CategoryTheory.Sites.LocallySurjective

/-! # Sheaf Base Cover Detection -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SheafBaseCoverDetection

noncomputable section

section

/-! Actual fppf test covers detect isomorphisms of sheaves. This lets
the original dual universal property be checked on its native base change. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {S : Scheme.{0}} {F G : Sheaf (Scheme.fppfTopology.over S) (Type 1)} (a : F ⟶ G)
    (hc : ∀ T : Over S, ∃ (U : Over S) (f : U ⟶ T),
      Flat f.left ∧ LocallyOfFinitePresentation f.left ∧ Surjective f.left ∧
      Function.Bijective (a.hom.app (.op U)))

include hc in
theorem sheaf_component_injective_of_covers (T : Over S) : Function.Injective (a.hom.app (.op T)) := by
  obtain ⟨U, f, hf, hfp, hs, hb⟩ := hc T
  let := hf
  let := hfp
  let := hs
  intro x y h
  apply RepresentationTheory.Theta.Geometric.FppfPicardLocality.fppfSheaf_map_injective F f
  apply hb.injective
  exact (a.hom.naturality_apply f.op x).trans
    ((congrArg (G.obj.map f.op) h).trans (a.hom.naturality_apply f.op y).symm)

include hc in
theorem sheaf_locallySurjective_of_covers : Sheaf.IsLocallySurjective a where
  imageSieve_mem {T} x := by
    obtain ⟨U, f, hf, hfp, hs, hb⟩ := hc T
    let := hf
    let := hfp
    let := hs
    apply (Scheme.fppfTopology.over S).superset_covering
      ((Sieve.generate_le_iff _ _).mpr ?_) (RepresentationTheory.Theta.Geometric.FppfPicardLocality.fppfSingletonOverSieve_mem f)
    intro V v hv
    obtain ⟨i⟩ := hv
    exact hb.surjective (G.obj.map f.op x)

include hc in
theorem sheaf_isIso_of_covers : IsIso a := by
  have (T : (Over S)ᵒᵖ) : Mono (a.hom.app T) :=
    ConcreteCategory.mono_of_injective _ (sheaf_component_injective_of_covers a hc T.unop)
  have : Mono a.hom := NatTrans.mono_of_mono_app a.hom
  have : Mono a := (sheafToPresheaf (Scheme.fppfTopology.over S) (Type 1)).mono_of_mono_map
    (inferInstanceAs (Mono a.hom))
  have : Sheaf.IsLocallySurjective a := sheaf_locallySurjective_of_covers a hc
  exact isIso_of_mono_of_epi a

end

/-! Restriction along an actual fppf base cover detects an isomorphism
of sheaves on all test schemes over the original base. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem sheaf_isIso_of_base_cover {S Y : Scheme.{0}} (p : Y ⟶ S)
    [Flat p] [LocallyOfFinitePresentation p] [Surjective p]
    {F G : Sheaf (Scheme.fppfTopology.over S) (Type 1)} (a : F ⟶ G)
    (ha : ∀ T : Over Y, Function.Bijective (a.hom.app (.op ((Over.map p).obj T)))) : IsIso a := by
  apply sheaf_isIso_of_covers a
  intro T
  let T' := (Over.pullback p).obj T
  let U := (Over.map p).obj T'
  let f : U ⟶ T := Over.homMk (pullback.fst T.hom p) pullback.condition
  exact ⟨U, f, inferInstanceAs (Flat (pullback.fst T.hom p)),
    inferInstanceAs (LocallyOfFinitePresentation (pullback.fst T.hom p)),
    inferInstanceAs (Surjective (pullback.fst T.hom p)), ha T'⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SheafBaseCoverDetection
