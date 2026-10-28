import Mathlib.AlgebraicGeometry.Properties
import Mathlib.Topology.Sets.OpenCover

/-! # Open Cover -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Integral.OpenCover.BundleCycles

/-! An open cover by integral schemes with a common point has an
integral ambient scheme. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

theorem isIntegral_of_openCover_commonPoint {X : Scheme.{0}} (C : X.OpenCover)
    (hI : ∀ i, IsIntegral (C.X i)) (x : X) (hx : ∀ i, x ∈ Set.range (C.f i)) : IsIntegral X := by
  have hred (i : C.I₀) : IsReduced (C.X i) := by
    let := hI i
    infer_instance
  let : IsReduced X := @IsReduced.of_openCover X C hred
  have hpre (i : C.I₀) : PreirreducibleSpace (C.f i).opensRange := by
    let := hI i
    let e := (C.f i).isOpenEmbedding.isEmbedding.toHomeomorph
    exact e.surjective.preirreducibleSpace e.continuous
  have hn : Pairwise (fun i j => ¬ Disjoint (C.f i).opensRange (C.f j).opensRange) := by
    intro i j _ h
    exact (show x ∈ (⊥ : X.Opens) from h.le_bot ⟨hx i, hx j⟩)
  let : PreirreducibleSpace X := PreirreducibleSpace.of_isOpenCover hn C.isOpenCover_opensRange hpre
  let : Nonempty X := ⟨x⟩
  let : IrreducibleSpace X := ⟨⟨x⟩⟩
  exact isIntegral_of_irreducibleSpace_of_isReduced X

end OAI.AlgebraicGeometry.Divisors.LineBundles.Integral.OpenCover.BundleCycles
