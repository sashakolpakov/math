import OAI.NumberTheory.PadicHodge.IntegralComparison.CokernelKernelHomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.ChainZeroCokernel

/-! # Computed Homology Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ComputedHomologyNaturality

noncomputable section

/-! Naturality of the original explicit cokernel/kernel homology
coordinates, including the degree-zero coordinates of a chain complex. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]

theorem shortComplex {κ : Type*} {c : ComplexShape κ}
    {K L : HomologicalComplex C c} (f : K ⟶ L) (i j k : κ)
    (hi : c.prev j = i) (hk : c.next j = k) :
    HomologicalComplex.homologyMap f j ≫ (L.homologyIsoSc' i j k hi hk).hom =
      (K.homologyIsoSc' i j k hi hk).hom ≫
        ShortComplex.homologyMap ((HomologicalComplex.shortComplexFunctor' C c i j k).map f) := by
  have h := (HomologicalComplex.natIsoSc' C c i j k hi hk).hom.naturality f
  let H := ShortComplex.homologyFunctor C
  exact (H.map_comp _ _).symm.trans
    ((congrArg H.map h).trans (H.map_comp _ _))

theorem chainZero {K L : ChainComplex C ℕ} (f : K ⟶ L) {X Y : C}
    (p : K.X 0 ⟶ X) (wp : K.d 1 0 ≫ p = 0)
    (hp : (ShortComplex.mk (K.d 1 0) p wp).Exact) [hp_epi : Epi p]
    (q : L.X 0 ⟶ Y) (wq : L.d 1 0 ≫ q = 0)
    (hq : (ShortComplex.mk (L.d 1 0) q wq).Exact) [hq_epi : Epi q]
    (a : X ⟶ Y) (ha : f.f 0 ≫ q = p ≫ a) :
    HomologicalComplex.homologyMap f 0 ≫ (ChainZeroCokernel.iso L q wq hq).hom =
      (ChainZeroCokernel.iso K p wp hp).hom ≫ a := by
  let d := ShortComplex.RightHomologyMapData.ofIsColimitCokernelCofork
    ((HomologicalComplex.shortComplexFunctor' C (.down ℕ) 1 0 0).map f)
    (K.shape 0 0 (by simp)) (CokernelCofork.ofπ p wp) hp.gIsCokernel
    (L.shape 0 0 (by simp)) (CokernelCofork.ofπ q wq) hq.gIsCokernel a ha
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun b => b ≫
      (ShortComplex.RightHomologyData.ofIsColimitCokernelCofork (L.sc' 1 0 0)
        (L.shape 0 0 (by simp)) (CokernelCofork.ofπ q wq) hq.gIsCokernel).homologyIso.hom)
      (shortComplex f 1 0 0 (by simp) (by simp))).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun b => (K.homologyIsoSc' 1 0 0 (by simp) (by simp)).hom ≫ b)
            d.homologyMap_comm).trans (Category.assoc _ _ _).symm)))

variable (S T : ShortComplex C) (f : S ⟶ T)
  {Q H Q' H' : C} (p : S.X₂ ⟶ Q) (a : Q ⟶ S.X₃) (ι : H ⟶ Q)
  (wp : S.f ≫ p = 0) (hp : (ShortComplex.mk S.f p wp).Exact) [ep : Epi p]
  (wι : ι ≫ a = 0) (hι : (ShortComplex.mk ι a wι).Exact) [mi : Mono ι]
  (fac : p ≫ a = S.g)
  (p' : T.X₂ ⟶ Q') (a' : Q' ⟶ T.X₃) (ι' : H' ⟶ Q')
  (wp' : T.f ≫ p' = 0) (hp' : (ShortComplex.mk T.f p' wp').Exact) [ep' : Epi p']
  (wι' : ι' ≫ a' = 0) (hι' : (ShortComplex.mk ι' a' wι').Exact) [mi' : Mono ι']
  (fac' : p' ≫ a' = T.g)
  (q : Q ⟶ Q') (h : H ⟶ H')
  (hqp : p ≫ q = f.τ₂ ≫ p') (hqa : q ≫ a' = a ≫ f.τ₃) (hh : h ≫ ι' = ι ≫ q)

include hqp hqa hh in
theorem cokernelKernel :
    ShortComplex.homologyMap f ≫ (CokernelKernelHomology.iso T p' a' ι' wp' hp' wι' hι' fac').hom =
      (CokernelKernelHomology.iso S p a ι wp hp wι hι fac).hom ≫ h := by
  let d : ShortComplex.RightHomologyMapData f
      (CokernelKernelHomology.data S p a ι wp hp wι hι fac)
      (CokernelKernelHomology.data T p' a' ι' wp' hp' wι' hι' fac') :=
    { φQ := q
      φH := h
      commp := hqp
      commg' := by
        change q ≫ hp'.gIsCokernel.desc (CokernelCofork.ofπ T.g T.zero) =
          hp.gIsCokernel.desc (CokernelCofork.ofπ S.g S.zero) ≫ f.τ₃
        rw [CokernelKernelHomology.desc_eq T p' a' wp' hp' fac',
          CokernelKernelHomology.desc_eq S p a wp hp fac]
        exact hqa
      commι := hh }
  exact d.homologyMap_comm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ComputedHomologyNaturality
