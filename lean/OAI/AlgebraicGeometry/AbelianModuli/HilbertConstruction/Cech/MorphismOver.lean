import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ModuleSections
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CechShort
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ModuleCechPullbackShort

/-! # Morphism Over -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.MorphismOver

noncomputable section

/-! A geometric map over the base and a refinement of its pulled-back
cover induce a map of the full ordinary Cech complexes. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
open _root_.AlgebraicGeometry.Scheme.Modules

universe u

namespace CechMorphismOver

variable {X Y S : Scheme.{u}} (f : Y ⟶ X) (π : X ⟶ S) (ρ : Y ⟶ S)
variable (h : f ≫ π = ρ) (M : X.Modules)
variable {ι κ : Type u} (U : ι → X.Opens) (V : κ → Y.Opens)
variable (r : κ → ι) (hr : ∀ j, V j ≤ f ⁻¹ᵁ U (r j))

include hr in
theorem intersection_le (n : ℕ) (a : Fin (n + 1) → κ) :
    (∏ᶜ fun k => V (a k)) ≤ f ⁻¹ᵁ (∏ᶜ fun k => U (r (a k))) := by
  change (∏ᶜ fun k => V (a k)) ≤ f ⁻¹ᵁ (∏ᶜ fun k => U ((r ∘ a) k))
  rw [(SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Hom.preimage_cechIntersection f) U n (r ∘ a)]
  rw [SheafCohomology.Cech.Cochains.TopologicalSpace.Opens.piObj_eq_iInf, SheafCohomology.Cech.Cochains.TopologicalSpace.Opens.piObj_eq_iInf]
  exact iInf_mono fun k => hr (a k)

def component (n : ℕ) : (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex π M U).X n ⟶
    (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex ρ ((Scheme.Modules.pullback f).obj M) V).X n :=
  Pi.lift fun a : Fin (n + 1) → κ =>
    Pi.π (fun b : Fin (n + 1) → ι => (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf π M).obj
      (op (∏ᶜ fun k => U (b k)))) (r ∘ a) ≫
    Quotients.FiniteDescent.ModuleSections.Construction.ModuleSectionsOver.map f π ρ h M (∏ᶜ fun k => U ((r ∘ a) k))
      (∏ᶜ fun k => V (a k)) (intersection_le f U V r hr n a)

theorem component_π (n : ℕ) (a : Fin (n + 1) → κ) :
    component f π ρ h M U V r hr n ≫
      Pi.π (fun b : Fin (n + 1) → κ =>
        (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf ρ ((Scheme.Modules.pullback f).obj M)).obj
          (op (∏ᶜ fun k => V (b k)))) a =
    Pi.π (fun b : Fin (n + 1) → ι => (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf π M).obj
      (op (∏ᶜ fun k => U (b k)))) (r ∘ a) ≫
    Quotients.FiniteDescent.ModuleSections.Construction.ModuleSectionsOver.map f π ρ h M (∏ᶜ fun k => U ((r ∘ a) k))
      (∏ᶜ fun k => V (a k)) (intersection_le f U V r hr n a) :=
  Pi.lift_comp_π _ _

theorem cosimplicial_π (n m : SimplexCategory) (a : n ⟶ m) (j : Fin (m.len + 1) → ι) :
    (((FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk _ U).cech).obj
      (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf π M)).map a) ≫
      Pi.π (fun b : Fin (m.len + 1) → ι => (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf π M).obj
        (op (∏ᶜ fun k => U (b k)))) j =
    Pi.π (fun b : Fin (n.len + 1) → ι => (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf π M).obj
        (op (∏ᶜ fun k => U (b k)))) (j ∘ a.toOrderHom.toFun) ≫
      (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf π M).map
        (Pi.lift fun k => Pi.π (fun l => U (j l)) (a.toOrderHom.toFun k)).op :=
  Pi.lift_comp_π _ _

def cosimplicialMap :
    ((FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk _ U).cech).obj
      (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf π M)) ⟶
    ((FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk _ V).cech).obj
      (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf ρ ((Scheme.Modules.pullback f).obj M))) where
  app n := component f π ρ h M U V r hr n.len
  naturality n m a := by
    apply Pi.hom_ext (f := fun j : Fin (m.len + 1) → κ =>
      (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf ρ ((Scheme.Modules.pullback f).obj M)).obj
        (op (∏ᶜ fun k => V (j k))))
    intro j
    conv_lhs =>
      rw [Category.assoc, component_π, ← Category.assoc, cosimplicial_π, Category.assoc]
    conv_rhs =>
      rw [Category.assoc, cosimplicial_π, ← Category.assoc, component_π, Category.assoc]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    exact Quotients.FiniteDescent.ModuleSections.Construction.ModuleSectionsOver.restrict f π ρ h M _ _ _ _ _

def map : SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex π M U ⟶
    SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex ρ ((Scheme.Modules.pullback f).obj M) V :=
  (AlgebraicTopology.alternatingCofaceMapComplex (ModuleCat.{u} Γ(S, ⊤))).map
    (cosimplicialMap f π ρ h M U V r hr)

theorem map_f (n : ℕ) : (CechMorphismOver.map f π ρ h M U V r hr).f n =
    component f π ρ h M U V r hr n := rfl

theorem map_value (n : ℕ) (z : (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex π M U).X n)
    (a : Fin (n + 1) → κ) :
    Quotients.FiniteDescent.CechTupleValues.Construction.CechTupleCoordinates.value ρ ((Scheme.Modules.pullback f).obj M) V n
      ((CechMorphismOver.map f π ρ h M U V r hr).f n z) a =
    Quotients.FiniteDescent.ModuleSections.Construction.ModuleSectionsOver.map f π ρ h M (∏ᶜ fun k => U ((r ∘ a) k))
      (∏ᶜ fun k => V (a k)) (intersection_le f U V r hr n a)
        (Quotients.FiniteDescent.CechTupleValues.Construction.CechTupleCoordinates.value π M U n z (r ∘ a)) :=
  ConcreteCategory.congr_hom (component_π f π ρ h M U V r hr n a) z

theorem mapped_value_index (n : ℕ) (z : (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex π M U).X n)
    (a b : Fin (n + 1) → ι) (hab : a = b) (W : Y.Opens)
    (ha : W ≤ f ⁻¹ᵁ (∏ᶜ fun k => U (a k)))
    (hb : W ≤ f ⁻¹ᵁ (∏ᶜ fun k => U (b k))) :
    Quotients.FiniteDescent.ModuleSections.Construction.ModuleSectionsOver.map f π ρ h M (∏ᶜ fun k => U (a k)) W ha
        (Quotients.FiniteDescent.CechTupleValues.Construction.CechTupleCoordinates.value π M U n z a) =
      Quotients.FiniteDescent.ModuleSections.Construction.ModuleSectionsOver.map f π ρ h M (∏ᶜ fun k => U (b k)) W hb
        (Quotients.FiniteDescent.CechTupleValues.Construction.CechTupleCoordinates.value π M U n z b) := by
  subst b
  rfl

theorem map_one (z : (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex π M U).X 1) (i j : κ) :
    Quotients.FiniteDescent.CechTuplePi.Construction.CechTupleCoordinates.one ρ ((Scheme.Modules.pullback f).obj M) V
        ((CechMorphismOver.map f π ρ h M U V r hr).f 1 z) i j =
      Quotients.FiniteDescent.ModuleCechD.Construction.ModuleCechPullback.schemeCechPullback1 f π ρ h M U V r hr
        (Quotients.FiniteDescent.CechTuplePi.Construction.CechTupleCoordinates.one π M U z) i j := by
  have hi : r ∘ ![i, j] = ![r i, r j] := by
    funext k
    fin_cases k <;> rfl
  let ha := (Quotients.FiniteDescent.CechTuplePi.Construction.CechTupleCoordinates.intersection_one V (i, j)).ge.trans
    (intersection_le f U V r hr 1 ![i, j])
  have hb : V i ⊓ V j ≤ f ⁻¹ᵁ (∏ᶜ fun k : Fin 2 => U (![r i, r j] k)) := by
    have ht := ha
    change V i ⊓ V j ≤ f ⁻¹ᵁ (∏ᶜ fun k : Fin 2 => U ((r ∘ ![i, j]) k)) at ht
    simpa only [hi] using ht
  have hn₁ := Quotients.FiniteDescent.ModuleSections.Construction.ModuleSectionsOver.restrict f π ρ h M
    (𝟙 (∏ᶜ fun k : Fin 2 => U ((r ∘ ![i, j]) k)))
    (eqToHom (Quotients.FiniteDescent.CechTuplePi.Construction.CechTupleCoordinates.intersection_one V (i, j)).symm)
    (intersection_le f U V r hr 1 ![i, j]) ha
    (Quotients.FiniteDescent.CechTupleValues.Construction.CechTupleCoordinates.value π M U 1 z (r ∘ ![i, j]))
  simp only [op_id] at hn₁
  rw [(SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf π M).map_id] at hn₁
  change Quotients.FiniteDescent.ModuleSections.Construction.ModuleSectionsOver.map f π ρ h M _ _ ha
    (Quotients.FiniteDescent.CechTupleValues.Construction.CechTupleCoordinates.value π M U 1 z (r ∘ ![i, j])) = _ at hn₁
  have hn₂ := Quotients.FiniteDescent.ModuleSections.Construction.ModuleSectionsOver.restrict f π ρ h M
    (eqToHom (Quotients.FiniteDescent.CechTuplePi.Construction.CechTupleCoordinates.intersection_one U (r i, r j)).symm)
    (𝟙 (V i ⊓ V j)) hb
    (Quotients.FiniteDescent.ModuleCechD.Construction.ModuleCechPullback.cechPullback_overlap_preimage f U V r hr i j)
    (Quotients.FiniteDescent.CechTupleValues.Construction.CechTupleCoordinates.value π M U 1 z ![r i, r j])
  simp only [op_id] at hn₂
  rw [(SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf ρ ((Scheme.Modules.pullback f).obj M)).map_id] at hn₂
  change _ = Quotients.FiniteDescent.ModuleSections.Construction.ModuleSectionsOver.map f π ρ h M _ _ hb
    (Quotients.FiniteDescent.CechTupleValues.Construction.CechTupleCoordinates.value π M U 1 z ![r i, r j]) at hn₂
  rw [Quotients.FiniteDescent.CechTupleValues.Construction.CechTupleCoordinates.one_apply, map_value]
  change _ = Quotients.FiniteDescent.ModuleSections.Construction.ModuleSectionsOver.map f π ρ h M (U (r i) ⊓ U (r j)) (V i ⊓ V j) _
    (Quotients.FiniteDescent.CechTuplePi.Construction.CechTupleCoordinates.one π M U z (r i) (r j))
  rw [Quotients.FiniteDescent.CechTupleValues.Construction.CechTupleCoordinates.one_apply]
  exact hn₁.symm.trans ((mapped_value_index f π ρ h M U 1 z _ _ hi _ ha hb).trans
    hn₂.symm)

theorem short_middle :
    ((HomologicalComplex.shortComplexFunctor' (ModuleCat.{u} Γ(S, ⊤))
      (ComplexShape.up ℕ) 0 1 2).map (CechMorphismOver.map f π ρ h M U V r hr)).τ₂ ≫
        (Quotients.FiniteDescent.CechShort.Construction.CechShortCoordinates.one ρ ((Scheme.Modules.pullback f).obj M) V).hom =
      (Quotients.FiniteDescent.CechShort.Construction.CechShortCoordinates.one π M U).hom ≫
        (Quotients.FiniteDescent.ModuleCechPullbackShort.Construction.ModuleCechPullback.shortMap f π ρ h M U V r hr).τ₂ := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  funext i j
  exact map_one f π ρ h M U V r hr z i j

end CechMorphismOver

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.MorphismOver
