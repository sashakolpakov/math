import OAI.AlgebraicGeometry.Quotients.FiniteDescent.IntegralImageReduced
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProperOpen
import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-! # Graph Closure Is -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.GraphClosureIs.Construction.GraphClosure

noncomputable section

/-! Closing the graph of a morphism from a nonempty affine open to a
proper scheme gives a proper integral modification of the source. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits

universe u

variable {S X P : Scheme.{u}}
variable (f : X ⟶ S) (p : P ⟶ S)
variable (U : X.Opens)
variable (j : U.toScheme ⟶ P) (hj : U.ι ≫ f = j ≫ p)

def graph : U.toScheme ⟶ pullback f p := pullback.lift U.ι j hj

theorem graph_fst : graph f p U j hj ≫ pullback.fst f p = U.ι := pullback.lift_fst _ _ _
theorem graph_snd : graph f p U j hj ≫ pullback.snd f p = j := pullback.lift_snd _ _ _

local instance graph_immersion : IsImmersion (graph f p U j hj) := by
  have : IsImmersion (graph f p U j hj ≫ pullback.fst f p) := by
    rw [graph_fst]
    infer_instance
  exact IsImmersion.of_comp (graph f p U j hj) (pullback.fst f p)

abbrev scheme : Scheme.{u} := (graph f p U j hj).image

def projection : scheme f p U j hj ⟶ X :=
  (graph f p U j hj).imageι ≫ pullback.fst f p

def map : scheme f p U j hj ⟶ P :=
  (graph f p U j hj).imageι ≫ pullback.snd f p

def chart : U.toScheme ⟶ scheme f p U j hj := (graph f p U j hj).toImage

theorem chart_projection : chart f p U j hj ≫ projection f p U j hj = U.ι := by
  rw [chart, projection, Scheme.Hom.toImage_imageι_assoc, graph_fst]

theorem chart_map : chart f p U j hj ≫ map f p U j hj = j := by
  rw [chart, map, Scheme.Hom.toImage_imageι_assoc, graph_snd]

theorem map_base : map f p U j hj ≫ p = projection f p U j hj ≫ f := by
  simp only [map, projection, Category.assoc, pullback.condition]

variable [QuasiSeparatedSpace X] [IsProper p] [CompactSpace U.toScheme]

local instance graph_quasiCompact : QuasiCompact (graph f p U j hj) := by
  have : QuasiCompact (graph f p U j hj ≫ pullback.fst f p) := by
    rw [graph_fst]
    infer_instance
  exact QuasiCompact.of_comp (graph f p U j hj) (pullback.fst f p)

omit [QuasiSeparatedSpace X] [CompactSpace U.toScheme] in
theorem proper : IsProper (projection f p U j hj) := by
  dsimp only [projection]
  infer_instance

omit [QuasiSeparatedSpace X] [CompactSpace U.toScheme] in
theorem map_isProper [IsProper f] : IsProper (map f p U j hj) := by
  have := proper f p U j hj
  have : IsProper (map f p U j hj ≫ p) := by
    rw [map_base]
    infer_instance
  exact IsProper.of_comp (map f p U j hj) p

theorem openImmersion : IsOpenImmersion (chart f p U j hj) := by
  dsimp only [chart]
  infer_instance

theorem dominant : IsDominant (chart f p U j hj) := by
  dsimp only [chart]
  infer_instance

theorem isIso_restrict : IsIso (projection f p U j hj ∣_ U) := by
  have := proper f p U j hj
  have := openImmersion f p U j hj
  have := dominant f p U j hj
  exact ProperOpen.Construction.ProperOpenSection.isIso_restrict (projection f p U j hj) U (chart f p U j hj)
    (chart_projection f p U j hj)

variable [IsIntegral X] [Nonempty U]

theorem integral : IsIntegral (scheme f p U j hj) := IntegralImageReduced.Construction.IntegralImage.integral _

omit [QuasiSeparatedSpace X] [CompactSpace U.toScheme] in
theorem surjective : Surjective (projection f p U j hj) := by
  have := proper f p U j hj
  have : IsDominant U.ι := AlgebraicGeometry.Opens.isDominant_ι
    (U.isOpen.dense (by simpa using ‹Nonempty U›))
  have : IsDominant (chart f p U j hj ≫ projection f p U j hj) := by
    rw [chart_projection]
    infer_instance
  have : IsDominant (projection f p U j hj) :=
    IsDominant.of_comp (chart f p U j hj) (projection f p U j hj)
  infer_instance

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.GraphClosureIs.Construction.GraphClosure
