import Mathlib.Algebra.Homology.ShortComplex.Preadditive

/-! # Short Complex Endpoint Homotopy -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.ShortComplexEndpointHomotopy.Construction.LocalSectionLifting

noncomputable section

section

/-! Additive functors preserve short-complex homotopy equivalences, without exactness assumptions. -/

open _root_.CategoryTheory

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
    (F : C ⥤ D) [F.Additive]
    {S T : ShortComplex C} {φ ψ : S ⟶ T}

def shortComplexHomotopyMap (h : ShortComplex.Homotopy φ ψ) :
    ShortComplex.Homotopy (F.mapShortComplex.map φ) (F.mapShortComplex.map ψ) where
  h₀ := F.map h.h₀
  h₁ := F.map h.h₁
  h₂ := F.map h.h₂
  h₃ := F.map h.h₃
  h₀_f := by
    change F.map h.h₀ ≫ F.map T.f = 0
    rw [← F.map_comp, h.h₀_f, F.map_zero]
  g_h₃ := by
    change F.map S.g ≫ F.map h.h₃ = 0
    rw [← F.map_comp, h.g_h₃, F.map_zero]
  comm₁ := by
    change F.map φ.τ₁ = F.map S.f ≫ F.map h.h₁ + F.map h.h₀ + F.map ψ.τ₁
    rw [← F.map_comp, ← F.map_add, ← F.map_add, h.comm₁]
  comm₂ := by
    change F.map φ.τ₂ = F.map S.g ≫ F.map h.h₂ + F.map h.h₁ ≫ F.map T.f + F.map ψ.τ₂
    rw [← F.map_comp, ← F.map_comp, ← F.map_add, ← F.map_add, h.comm₂]
  comm₃ := by
    change F.map φ.τ₃ = F.map h.h₃ + F.map h.h₂ ≫ F.map T.g + F.map ψ.τ₃
    rw [← F.map_comp, ← F.map_add, ← F.map_add, h.comm₃]

def shortComplexCompositeHomotopyMap (φ : S ⟶ T) (ψ : T ⟶ S)
    (h : ShortComplex.Homotopy (φ ≫ ψ) (𝟙 S)) :
    ShortComplex.Homotopy (F.mapShortComplex.map φ ≫ F.mapShortComplex.map ψ)
      (𝟙 (F.mapShortComplex.obj S)) where
  h₀ := F.map h.h₀
  h₁ := F.map h.h₁
  h₂ := F.map h.h₂
  h₃ := F.map h.h₃
  h₀_f := by
    change F.map h.h₀ ≫ F.map S.f = 0
    rw [← F.map_comp, h.h₀_f, F.map_zero]
  g_h₃ := by
    change F.map S.g ≫ F.map h.h₃ = 0
    rw [← F.map_comp, h.g_h₃, F.map_zero]
  comm₁ := by
    change F.map φ.τ₁ ≫ F.map ψ.τ₁ = F.map S.f ≫ F.map h.h₁ + F.map h.h₀ + 𝟙 (F.obj S.X₁)
    simpa only [ShortComplex.comp_τ₁, ShortComplex.id_τ₁,
      F.map_comp, F.map_add, F.map_id] using congrArg F.map h.comm₁
  comm₂ := by
    change F.map φ.τ₂ ≫ F.map ψ.τ₂ = F.map S.g ≫ F.map h.h₂ + F.map h.h₁ ≫ F.map S.f + 𝟙 (F.obj S.X₂)
    simpa only [ShortComplex.comp_τ₂, ShortComplex.id_τ₂,
      F.map_comp, F.map_add, F.map_id] using congrArg F.map h.comm₂
  comm₃ := by
    change F.map φ.τ₃ ≫ F.map ψ.τ₃ = F.map h.h₃ + F.map h.h₂ ≫ F.map S.g + 𝟙 (F.obj S.X₃)
    simpa only [ShortComplex.comp_τ₃, ShortComplex.id_τ₃,
      F.map_comp, F.map_add, F.map_id] using congrArg F.map h.comm₃

def shortComplexHomotopyEquivMap (e : ShortComplex.HomotopyEquiv S T) :
    ShortComplex.HomotopyEquiv (F.mapShortComplex.obj S) (F.mapShortComplex.obj T) where
  hom := F.mapShortComplex.map e.hom
  inv := F.mapShortComplex.map e.inv
  homotopyHomInvId := shortComplexCompositeHomotopyMap F e.hom e.inv e.homotopyHomInvId
  homotopyInvHomId := shortComplexCompositeHomotopyMap F e.inv e.hom e.homotopyInvHomId

def shortComplexHomotopyEquivHomologyIso
    [S.HasHomology] [T.HasHomology] (e : ShortComplex.HomotopyEquiv S T) : S.homology ≅ T.homology where
  hom := ShortComplex.homologyMap e.hom
  inv := ShortComplex.homologyMap e.inv
  hom_inv_id := by
    rw [← ShortComplex.homologyMap_comp, e.homotopyHomInvId.homologyMap_congr,
      ShortComplex.homologyMap_id]
  inv_hom_id := by
    rw [← ShortComplex.homologyMap_comp, e.homotopyInvHomId.homologyMap_congr,
      ShortComplex.homologyMap_id]

def shortComplexHomotopyEquivMapHomologyIso
    [(F.mapShortComplex.obj S).HasHomology] [(F.mapShortComplex.obj T).HasHomology]
    (e : ShortComplex.HomotopyEquiv S T) :
    (F.mapShortComplex.obj S).homology ≅ (F.mapShortComplex.obj T).homology :=
  shortComplexHomotopyEquivHomologyIso (shortComplexHomotopyEquivMap F e)

end

/-! Homotopy equivalences with no endpoint error also preserve degree-zero cycles. -/

open _root_.CategoryTheory

variable {C : Type*} [Category* C] [Preadditive C]
    {S T U : ShortComplex C}

theorem shortComplexHomotopyEquiv_trans_hom_h₀
    (e : ShortComplex.HomotopyEquiv S T) (e' : ShortComplex.HomotopyEquiv T U)
    (h : e.homotopyHomInvId.h₀ = 0) (h' : e'.homotopyHomInvId.h₀ = 0) :
    (e.trans e').homotopyHomInvId.h₀ = 0 := by
  simp [ShortComplex.HomotopyEquiv.trans, ShortComplex.Homotopy.trans,
    ShortComplex.Homotopy.ofEq, ShortComplex.Homotopy.compLeft,
    ShortComplex.Homotopy.compRight, h, h']

theorem shortComplexHomotopyEquiv_trans_inv_h₀
    (e : ShortComplex.HomotopyEquiv S T) (e' : ShortComplex.HomotopyEquiv T U)
    (h : e.homotopyInvHomId.h₀ = 0) (h' : e'.homotopyInvHomId.h₀ = 0) :
    (e.trans e').homotopyInvHomId.h₀ = 0 := by
  simp [ShortComplex.HomotopyEquiv.trans, ShortComplex.Homotopy.trans,
    ShortComplex.Homotopy.ofEq, ShortComplex.Homotopy.compLeft,
    ShortComplex.Homotopy.compRight, h, h']

variable {D : Type*} [Category* D] [Preadditive D] (F : C ⥤ D) [F.Additive]

theorem shortComplexHomotopyEquivMap_hom_h₀
    (e : ShortComplex.HomotopyEquiv S T) (h : e.homotopyHomInvId.h₀ = 0) :
    (shortComplexHomotopyEquivMap F e).homotopyHomInvId.h₀ = 0 := by
  change F.map e.homotopyHomInvId.h₀ = 0
  rw [h, F.map_zero]

theorem shortComplexHomotopyEquivMap_inv_h₀
    (e : ShortComplex.HomotopyEquiv S T) (h : e.homotopyInvHomId.h₀ = 0) :
    (shortComplexHomotopyEquivMap F e).homotopyInvHomId.h₀ = 0 := by
  change F.map e.homotopyInvHomId.h₀ = 0
  rw [h, F.map_zero]

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.ShortComplexEndpointHomotopy.Construction.LocalSectionLifting
