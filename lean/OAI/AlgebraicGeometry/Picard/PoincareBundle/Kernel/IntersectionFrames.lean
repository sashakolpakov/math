import OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.FramePairing

/-! # Intersection Frames -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.IntersectionFrames

noncomputable section

/-!
# Comparing two actual kernel frames on the same scheme-theoretic kernel intersection
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.FramePairing

variable {S : Scheme.{u}} {H K A X : Over S} (i : H ⟶ A) (j : K ⟶ X)
  (L : Line.Bundles.LineBundle (A ⊗ X).left)
  (sh : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (H ⊗ X).left ≅ (Scheme.Modules.pullback (i ⊗ₘ 𝟙 X).left).obj L.sheaf)
  (sv : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (A ⊗ K).left ≅ (Scheme.Modules.pullback (𝟙 A ⊗ₘ j).left).obj L.sheaf)

/-- The common restriction is an actual line bundle on the full subgroup product. -/
def intersectionLine : Line.Bundles.LineBundle (H ⊗ K).left := L.pullback (i ⊗ₘ j).left

theorem horizontal_factor : (𝟙 H ⊗ₘ j) ≫ (i ⊗ₘ 𝟙 X) = i ⊗ₘ j := by
  rw [tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]

theorem vertical_factor : (i ⊗ₘ 𝟙 K) ≫ (𝟙 A ⊗ₘ j) = i ⊗ₘ j := by
  rw [tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]

/-- Restrict the first normalized frame and identify its pullback with the common intersection line. -/
def horizontalFrame : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (H ⊗ K).left ≅ (intersectionLine i j L).sheaf :=
  (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso (𝟙 H ⊗ₘ j).left).symm ≪≫
    (Scheme.Modules.pullback (𝟙 H ⊗ₘ j).left).mapIso sh ≪≫
    (Scheme.Modules.pullbackComp (𝟙 H ⊗ₘ j).left (i ⊗ₘ 𝟙 X).left).app L.sheaf ≪≫
    (Scheme.Modules.pullbackCongr (congrArg Over.Hom.left (horizontal_factor i j))).app L.sheaf

/-- Restrict the second normalized frame to exactly the same actual line sheaf. -/
def verticalFrame : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (H ⊗ K).left ≅ (intersectionLine i j L).sheaf :=
  (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso (i ⊗ₘ 𝟙 K).left).symm ≪≫
    (Scheme.Modules.pullback (i ⊗ₘ 𝟙 K).left).mapIso sv ≪≫
    (Scheme.Modules.pullbackComp (i ⊗ₘ 𝟙 K).left (𝟙 A ⊗ₘ j).left).app L.sheaf ≪≫
    (Scheme.Modules.pullbackCongr (congrArg Over.Hom.left (vertical_factor i j))).app L.sheaf

/-- The scheme-valued obstruction is the actual unit ratio of these two canonical restrictions. -/
def obstruction {T : Over S} (a : T ⟶ H) (b : T ⟶ K) : Γ(T.left, ⊤)ˣ :=
  Biextension.FramePairing.pairingValue (intersectionLine i j L) (horizontalFrame i j L sh) (verticalFrame i j L sv) a b

/-- The kernel-intersection obstruction is natural for every map of test schemes. -/
theorem obstruction_naturality {T T' : Over S} (t : T' ⟶ T) (a : T ⟶ H) (b : T ⟶ K) :
    obstruction i j L sh sv (t ≫ a) (t ≫ b) = Units.map t.left.appTop.hom (obstruction i j L sh sv a b) :=
  Biextension.FramePairing.pairingValue_naturality (intersectionLine i j L) (horizontalFrame i j L sh) (verticalFrame i j L sv)
    t a b

/-- Triviality on all scheme-valued pairs identifies the two actual intersection frames. -/
theorem obstruction_trivial_iff :
    (∀ (T : Over S) (a : T ⟶ H) (b : T ⟶ K), obstruction i j L sh sv a b = 1) ↔
      horizontalFrame i j L sh = verticalFrame i j L sv :=
  Biextension.FramePairing.pairingValue_all_one_iff (intersectionLine i j L) (horizontalFrame i j L sh) (verticalFrame i j L sv)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.IntersectionFrames
