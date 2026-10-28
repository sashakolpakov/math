import OAI.AlgebraicGeometry.Comparison.Betti.FlasqueBiproduct
import Mathlib.CategoryTheory.Preadditive.Biproducts

/-! # Flasque Finite Coproduct -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.FlasqueFiniteCoproduct

noncomputable section

/-! Finite coproducts of flasque complex sheaves are flasque, by componentwise section lifting. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.TopologicalSpace

variable {X : TopCat.{0}} {ι : Type} [Finite ι]
  (F : ι → FlasqueBiproduct.ComplexSheaves X) (hF : ∀ j, TopCat.Sheaf.IsFlasque (F j))

local instance finiteSheafBiproduct : HasBiproduct F := HasBiproduct.of_hasProduct F

include hF

theorem finiteBiproduct_flasque : TopCat.Sheaf.IsFlasque (⨁ F) := by
  classical
  let := Fintype.ofFinite ι
  constructor
  intro U V i
  apply (ModuleCat.epi_iff_surjective _).mpr
  intro s
  have hlift (j : ι) : ∃ a, (F j).obj.map i a = (biproduct.π F j).hom.app V s := by
    have := hF j
    exact (ModuleCat.epi_iff_surjective ((F j).obj.map i)).mp inferInstance _
  choose a ha using hlift
  refine ⟨∑ j, (biproduct.ι F j).hom.app U (a j), ?_⟩
  rw [map_sum]
  have hn (j : ι) :
      (⨁ F).obj.map i ((biproduct.ι F j).hom.app U (a j)) =
        (biproduct.ι F j).hom.app V ((biproduct.π F j).hom.app V s) := by
    have h := ConcreteCategory.congr_hom ((biproduct.ι F j).hom.naturality i) (a j)
    change (biproduct.ι F j).hom.app V ((F j).obj.map i (a j)) =
      (⨁ F).obj.map i ((biproduct.ι F j).hom.app U (a j)) at h
    exact h.symm.trans (congrArg ((biproduct.ι F j).hom.app V) (ha j))
  simp only [hn]
  let ev : ((⨁ F) ⟶ (⨁ F)) →+ (⨁ F).obj.obj V :=
    { toFun := fun k => k.hom.app V s
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have ht := congrArg ev (biproduct.total (f := F))
  rw [map_sum] at ht
  exact ht

theorem finiteCoproduct_flasque : TopCat.Sheaf.IsFlasque (∐ F) := by
  have := finiteBiproduct_flasque F hF
  exact FlasqueBiproduct.flasque_of_iso (biproduct.isoCoproduct F)

end

end OAI.AlgebraicGeometry.Comparison.Betti.FlasqueFiniteCoproduct
