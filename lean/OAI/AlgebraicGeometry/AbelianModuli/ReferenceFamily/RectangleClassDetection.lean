import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.RegularBoundary
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RectangleBoundaryShuffle

/-! # Rectangle Class Detection -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RectangleClassDetection

noncomputable section

/-! A zero original H2 class on an affine rectangular cover has
zero mixed tensor projection. The actual product opens and their
acyclicity are constructed from the original affine covers. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

local instance rectangleCohomologyAddGroup {X : TopCat.{0}}
    (F : TopCat.Sheaf AddCommGrpCat.{0} X) (n : ℕ) :
    AddCommGroup (CategoryTheory.Sheaf.H F n) :=
  inferInstanceAs (AddCommGroup ((CategoryTheory.Sheaf.functorH
    (Opens.grothendieckTopology X) n : _ ⥤ AddCommGrpCat.{0}).obj F))

variable {k : Type} [Field k] {X Y : Scheme.{0}}
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    {I J : Type} (U : I → X.Opens) (V : J → Y.Opens)

theorem rectangleOpenCover_affine (hU : ∀ i, IsAffineOpen (U i)) (hV : ∀ j, IsAffineOpen (V j))
    (p : Σ _ : I, J) : IsAffineOpen (Quotients.FiniteDescent.CubeProductCechCocycles.Construction.CubeCech.rectangleOpenCover f g U V p) := by
  let : IsAffine (U p.1).toScheme := hU p.1
  let : IsAffine (V p.2).toScheme := hV p.2
  let : IsAffine (⊤ : (Spec (.of k)).Opens).toScheme := isAffineOpen_top _
  exact .of_isIso
    (Scheme.Hom.isPullback_resLE (IsPullback.of_hasPullback f g)
      (show V p.2 ≤ g ⁻¹ᵁ ⊤ by simp) (show U p.1 ≤ f ⁻¹ᵁ ⊤ by simp)
      (rfl : Quotients.FiniteDescent.CubeProductCechCocycles.Construction.CubeCech.rectangleOpenCover f g U V p = _)).isoPullback.hom

theorem rectangleOpenCover_covers (hU : iSup U = ⊤) (hV : iSup V = ⊤) :
    iSup (Quotients.FiniteDescent.CubeProductCechCocycles.Construction.CubeCech.rectangleOpenCover f g U V) = ⊤ := by
  apply top_unique
  intro x _
  have hx : (pullback.fst f g) x ∈ iSup U := by rw [hU]; trivial
  have hy : (pullback.snd f g) x ∈ iSup V := by rw [hV]; trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
  obtain ⟨j, hj⟩ := Opens.mem_iSup.mp hy
  exact Opens.mem_iSup.mpr ⟨⟨i, j⟩, hi, hj⟩

variable [(pullback f g).IsSeparated]
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

theorem rectangleTripleShuffle_zero_of_sheafClass_zero
    (hU : ∀ i, IsAffineOpen (U i)) (hV : ∀ j, IsAffineOpen (V j))
    (hUU : ∀ i i', IsAffineOpen (U i ⊓ U i')) (hVV : ∀ j j', IsAffineOpen (V j ⊓ V j'))
    (hcU : iSup U = ⊤) (hcV : iSup V = ⊤)
    (w : RectangleBoundaryShuffle.rectangleOrdinaryCech2 f g U V)
    (hw : DivisorClass.Chern.Abelian.CechCoordinates.abelianCechDelta (Dual.UnitCechClasses.ringAdditiveSheaf (pullback f g).sheaf).obj
      (Quotients.FiniteDescent.CubeProductCechCocycles.Construction.CubeCech.rectangleOpenCover f g U V) 2
      (Regular.BoundaryShuffle.regularTripleCechCochain (pullback f g) (Quotients.FiniteDescent.CubeProductCechCocycles.Construction.CubeCech.rectangleOpenCover f g U V) w) = 0)
    (hclass : DivisorClass.Chern.Abelian.CechClasses.abelianCechSheafClass (Quotients.FiniteDescent.CubeProductCechCocycles.Construction.CubeCech.rectangleOpenCover f g U V)
      (Dual.UnitCechClasses.ringAdditiveSheaf (pullback f g).sheaf) (rectangleOpenCover_covers f g U V hcU hcV) 1
      (Regular.BoundaryShuffle.regularTripleCechCochain (pullback f g) (Quotients.FiniteDescent.CubeProductCechCocycles.Construction.CubeCech.rectangleOpenCover f g U V) w) hw = 0) :
    RectangleMixedClassProjection.rectangleMixedClassProjection f g U V hUU hVV (RectangleBoundaryShuffle.rectangleTripleShuffle f g U V w) = 0 := by
  obtain ⟨v, hv⟩ := Affine.RegularBoundary.regularTriplePrimitive_of_affine_sheafClass_zero (pullback f g)
    (Quotients.FiniteDescent.CubeProductCechCocycles.Construction.CubeCech.rectangleOpenCover f g U V) (rectangleOpenCover_covers f g U V hcU hcV)
    (rectangleOpenCover_affine f g U V hU hV) w hw hclass
  exact RectangleBoundaryShuffle.rectangleTripleShuffle_boundary_class_zero f g U V hU hV hUU hVV v w hv

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RectangleClassDetection
