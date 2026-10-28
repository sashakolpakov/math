import OAI.ArithmeticGeometry.Descent.CMVariety.EnhancedCoefficientComparisons
import OAI.ArithmeticGeometry.Descent.CMVariety.EnhancementExtension

/-! # Enhanced Tuple Extension -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety

noncomputable section

/-! Add the actual CM tuple to enhanced polarized full-level data and
preserve the complete object through its arithmetic fiber comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {g N r m : ℕ} {δ : Fin g → ℕ} {S T : Scheme}

def ModuliObjects.Abelian.EnhancedAbelianData.withExtraEndomorphisms (A : ModuliObjects.Abelian.EnhancedAbelianData g δ N r S)
    (a : AbelianEndomorphism.AbelianEndomorphismTuple (Fin m) A.polarized.abelian) :
    ModuliObjects.Abelian.EnhancedAbelianData g δ N (r + m) S where
  polarized := A.polarized
  endomorphism := Fin.addCases A.endomorphism a.map
  endomorphism_group i := by
    refine Fin.addCases ?_ ?_ i
    · intro j
      simpa only [Fin.addCases_left] using A.endomorphism_group j
    · intro j
      simpa only [Fin.addCases_right] using a.group j

theorem CoefficientEndomorphismComparison.Abelian.ConjugateEndomorphisms.equivariant
    {C : Type*} [Category* C] {X Y : C} (e : X ≅ Y) (a : X ⟶ X) (b : Y ⟶ Y)
    (h : CoefficientEndomorphismComparison.Abelian.ConjugateEndomorphisms e a b) : a ≫ e.hom = e.hom ≫ b := by
  dsimp only [CoefficientEndomorphismComparison.Abelian.ConjugateEndomorphisms] at h
  rw [h]
  simp only [Category.assoc, e.inv_hom_id, Category.comp_id]

def ModuliObjects.Abelian.EnhancedAbelianIso.withExtraEndomorphisms
    {A B : ModuliObjects.Abelian.EnhancedAbelianData g δ N r S} (e : ModuliObjects.Abelian.EnhancedAbelianIso A B)
    (a : AbelianEndomorphism.AbelianEndomorphismTuple (Fin m) A.polarized.abelian)
    (b : AbelianEndomorphism.AbelianEndomorphismTuple (Fin m) B.polarized.abelian)
    (h : AbelianEndomorphism.ConjugateAbelianTuples e.polarized.abelian a b) :
    ModuliObjects.Abelian.EnhancedAbelianIso (A.withExtraEndomorphisms a) (B.withExtraEndomorphisms b) where
  polarized := e.polarized
  equivariant i := by
    refine Fin.addCases ?_ ?_ i
    · intro j
      simpa only [ModuliObjects.Abelian.EnhancedAbelianData.withExtraEndomorphisms, Fin.addCases_left] using e.equivariant j
    · intro j
      simpa only [ModuliObjects.Abelian.EnhancedAbelianData.withExtraEndomorphisms, Fin.addCases_right] using
        CoefficientEndomorphismComparison.Abelian.ConjugateEndomorphisms.equivariant e.polarized.abelian (a.map j) (b.map j) (h j)

def ModuliObjects.Abelian.EnhancedAbelianData.pullbackWithExtraIso
    (A : ModuliObjects.Abelian.EnhancedAbelianData g δ N r S)
    (a : AbelianEndomorphism.AbelianEndomorphismTuple (Fin m) A.polarized.abelian) (f : T ⟶ S) :
    ModuliObjects.Abelian.EnhancedAbelianIso ((A.withExtraEndomorphisms a).pullback f)
      ((A.pullback f).withExtraEndomorphisms (a.pullback f)) where
  polarized := AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso.refl (A.polarized.pullback f)
  equivariant i := by
    change (Over.pullback f).map (Fin.addCases A.endomorphism a.map i) ≫ 𝟙 _ =
      𝟙 _ ≫ Fin.addCases (fun j => (Over.pullback f).map (A.endomorphism j))
        (fun j => (Over.pullback f).map (a.map j)) i
    simp only [Category.comp_id, Category.id_comp]
    refine Fin.addCases ?_ ?_ i
    · intro j
      simp only [Fin.addCases_left]
    · intro j
      simp only [Fin.addCases_right]

def EnhancedTupleExtension.Abelian.enhancedFiberIsoWithExtraTuple
    (G : ModuliObjects.Abelian.EnhancedAbelianData g δ N r S) (p : T ⟶ S)
    (A : ModuliObjects.Abelian.EnhancedAbelianData g δ N r T) (e : ModuliObjects.Abelian.EnhancedAbelianIso (G.pullback p) A)
    (a : AbelianEndomorphism.AbelianEndomorphismTuple (Fin m) G.polarized.abelian)
    (k : AbelianEndomorphism.AbelianEndomorphismTuple (Fin m) A.polarized.abelian)
    (h : AbelianEndomorphism.ConjugateAbelianTuples e.polarized.abelian (a.pullback p) k) :
    ModuliObjects.Abelian.EnhancedAbelianIso ((G.withExtraEndomorphisms a).pullback p) (A.withExtraEndomorphisms k) :=
  (G.pullbackWithExtraIso a p).trans (e.withExtraEndomorphisms (a.pullback p) k h)

theorem EnhancedTupleExtension.Abelian.enhancedFiberIsoWithExtraTuple_abelian
    (G : ModuliObjects.Abelian.EnhancedAbelianData g δ N r S) (p : T ⟶ S)
    (A : ModuliObjects.Abelian.EnhancedAbelianData g δ N r T) (e : ModuliObjects.Abelian.EnhancedAbelianIso (G.pullback p) A)
    (a : AbelianEndomorphism.AbelianEndomorphismTuple (Fin m) G.polarized.abelian)
    (k : AbelianEndomorphism.AbelianEndomorphismTuple (Fin m) A.polarized.abelian)
    (h : AbelianEndomorphism.ConjugateAbelianTuples e.polarized.abelian (a.pullback p) k) :
    (EnhancedTupleExtension.Abelian.enhancedFiberIsoWithExtraTuple G p A e a k h).polarized.abelian = e.polarized.abelian := by
  apply Iso.ext
  change 𝟙 _ ≫ e.polarized.abelian.hom = e.polarized.abelian.hom
  exact Category.id_comp _

end

end OAI.ArithmeticGeometry.Descent.CMVariety
