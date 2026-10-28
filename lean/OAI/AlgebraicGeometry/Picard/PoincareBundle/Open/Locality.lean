import OAI.AlgebraicGeometry.Picard.PoincareBundle.Functor

/-! # Locality -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Open.Locality

noncomputable section

/-! Equality of relative Picard sections can be checked on a Zariski cover of the test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite _root_.TopologicalSpace

universe u

variable {S : Scheme.{u}} (T : Over S)

/-- An open subscheme retains its specified map to the base. -/
def openObject (U : T.left.Opens) : Over S := Over.mk (U.ι ≫ T.hom)

/-- The inclusion of an open test subscheme. -/
def openInclusion (U : T.left.Opens) : openObject T U ⟶ T := Over.homMk U.ι

/-- A Zariski cover of a test scheme is a cover in the relative fppf site. -/
theorem openCover_mem {I : Type u} (U : I → T.left.Opens) (hU : IsOpenCover U) :
    Sieve.ofArrows (fun i => openObject T (U i)) (fun i => openInclusion T (U i)) ∈
      (Scheme.fppfTopology.over S) T := by
  rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
  exact (Precoverage.toGrothendieck_mono Scheme.zariskiPrecoverage_le_fppfPrecoverage)
    _ (T.left.openCoverOfIsOpenCover U hU).mem_grothendieckTopology

/-- Sections of any relative fppf sheaf are determined by their open restrictions. -/
theorem sections_ext (F : Sheaf (Scheme.fppfTopology.over S) (Type (u + 1)))
    {I : Type u} (U : I → T.left.Opens) (hU : IsOpenCover U)
    {x y : F.obj.obj (op T)}
    (h : ∀ i, F.obj.map (openInclusion T (U i)).op x =
      F.obj.map (openInclusion T (U i)).op y) : x = y := by
  let a : PUnit.{u + 2} ⟶ F.obj.obj (op T) := ↾(fun _ => x)
  let b : PUnit.{u + 2} ⟶ F.obj.obj (op T) := ↾(fun _ => y)
  have hab : a = b := F.property.hom_ext_ofArrows
    (fun i => openInclusion T (U i)) (openCover_mem T U hU) (by
      intro i
      apply ConcreteCategory.ext_apply
      intro z
      exact h i)
  exact congrArg (fun c => c PUnit.unit) hab

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Open.Locality
