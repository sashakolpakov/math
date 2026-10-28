import OAI.NumberTheory.PadicHodge.GeometricComparison.ProductFiltration
import OAI.NumberTheory.PadicHodge.GeometricComparison.FirstHodgeNumber

/-! # Filtration Bounds -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.FiltrationBounds.FiltrationTransport

noncomputable section

/-! Degree-zero and degree-two bounds persist under actual subspace and product filtrations. -/

variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

theorem restrict_top (F : Linear.FiniteFiltration K V) (U : Submodule K V) (i : ℤ) (hi : F.step i = ⊤) :
    (F.restrict U).step i = ⊤ := by
  change (F.step i).comap U.subtype = ⊤
  rw [hi, Submodule.comap_top]

theorem restrict_bot (F : Linear.FiniteFiltration K V) (U : Submodule K V) (i : ℤ) (hi : F.step i = ⊥) :
    (F.restrict U).step i = ⊥ := by
  change (F.step i).comap U.subtype = ⊥
  rw [hi, Submodule.comap_bot, Submodule.ker_subtype]

theorem product_top (F : Linear.FiniteFiltration K V) (G : Linear.FiniteFiltration K W) (i : ℤ)
    (hF : F.step i = ⊤) (hG : G.step i = ⊤) : (ProductFiltration.FiltrationTransport.product F G).step i = ⊤ := by
  change (F.step i).prod (G.step i) = ⊤
  rw [hF, hG, Submodule.prod_top]

theorem product_bot (F : Linear.FiniteFiltration K V) (G : Linear.FiniteFiltration K W) (i : ℤ)
    (hF : F.step i = ⊥) (hG : G.step i = ⊥) : (ProductFiltration.FiltrationTransport.product F G).step i = ⊥ := by
  change (F.step i).prod (G.step i) = ⊥
  rw [hF, hG, Submodule.prod_bot]

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.FiltrationBounds.FiltrationTransport
