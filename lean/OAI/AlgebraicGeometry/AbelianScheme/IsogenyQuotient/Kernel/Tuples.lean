import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Kernel.Product

/-! # Tuples -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Kernel.Tuples.Construction

noncomputable section

/-!
Assemble finitely many separated torsion kernels. The model is an iterated
fiber product of the original models; lifted projectors prove that its
map into the abelian scheme is a monomorphism. The common torsion exponent
and arbitrary parameter base change are preserved by the construction.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

variable {S : Scheme.{u}} {A P : Over S} [GrpObj A] [IsCommMonObj A]

def trivialRelativeSubgroup : TorsionQuotient.SubgroupFunctor.RelativeSubgroup A P where
  points _ _ := ⊥
  naturality := by
    intro X Y f t a ha
    change a = 1 at ha
    change f ≫ a = 1
    rw [ha, MonObj.comp_one]

def trivialRelativeSubgroup_model : (trivialRelativeSubgroup (A := A) (P := P)).Model where
  carrier := P
  toBase := 𝟙 P
  toGroup := 1
  finite := by change IsFinite (𝟙 P.left); infer_instance
  flat := by change Flat (𝟙 P.left); infer_instance
  finitePresentation := by change LocallyOfFinitePresentation (𝟙 P.left); infer_instance
  jointly_monic _ _ _ h _ := by simpa only [Category.comp_id] using h
  points_iff X t a := by
    change a = 1 ↔ ∃ h : X ⟶ P, h ≫ 𝟙 P = t ∧ h ≫ (1 : P ⟶ A) = a
    simp only [Category.comp_id, MonObj.comp_one]
    constructor
    · intro ha
      exact ⟨t, rfl, ha.symm⟩
    · rintro ⟨_, _, ha⟩
      exact ha.symm

def AnnihilatedBy (F : TorsionQuotient.SubgroupFunctor.RelativeSubgroup A P) (p : A ⟶ A) : Prop :=
  ∀ (X : Over S) (t : X ⟶ P) (x : X ⟶ A), x ∈ F.points X t → x ≫ p = 1

theorem annihilatedBy_iff_model_equation
    (F : TorsionQuotient.SubgroupFunctor.RelativeSubgroup A P) (R : F.Model) (p : A ⟶ A) :
    AnnihilatedBy F p ↔ R.toGroup ≫ p = 1 := by
  constructor
  · intro h
    exact h R.carrier R.toBase R.toGroup
      ((R.points_iff _ _ _).mpr ⟨𝟙 _, Category.id_comp _, Category.id_comp _⟩)
  · intro h X t x hx
    obtain ⟨r, _, hrx⟩ := (R.points_iff X t x).mp hx
    rw [← hrx, Category.assoc, h, MonObj.comp_one]

def tupleKernel : (s : ℕ) → (Fin s → TorsionQuotient.SubgroupFunctor.RelativeSubgroup A P) → TorsionQuotient.SubgroupFunctor.RelativeSubgroup A P
  | 0, _ => trivialRelativeSubgroup
  | s + 1, F => Product.Construction.relativeKernelProduct (F 0) (tupleKernel s (fun i => F i.succ))

theorem tupleKernel_killed
    (s : ℕ) (F : Fin s → TorsionQuotient.SubgroupFunctor.RelativeSubgroup A P)
    (n : ℕ) (hF : ∀ i, (F i).KilledBy n) : (Construction.tupleKernel s F).KilledBy n := by
  induction s with
  | zero =>
      intro X t x hx
      change x = 1 at hx
      rw [hx, one_pow]
  | succ s ih =>
      exact Product.Construction.relativeKernelProduct_killed (F 0) (Construction.tupleKernel s (fun i => F i.succ)) n
        (hF 0) (ih _ (fun i => hF i.succ))

theorem tupleKernel_annihilated
    (s : ℕ) (F : Fin s → TorsionQuotient.SubgroupFunctor.RelativeSubgroup A P)
    (p : A ⟶ A) [IsMonHom p] (hF : ∀ i, AnnihilatedBy (F i) p) :
    AnnihilatedBy (Construction.tupleKernel s F) p := by
  induction s with
  | zero =>
      intro X t x hx
      change x = 1 at hx
      rw [hx, MonObj.one_comp]
  | succ s ih =>
      intro X t x hx
      obtain ⟨y, hy, z, hz, rfl⟩ := hx
      rw [MonObj.mul_comp, hF 0 X t y hy,
        ih (fun i => F i.succ) (fun i => hF i.succ) X t z hz, one_mul]

/-- The simultaneous kernel has a finite locally free model when local
projectors separate its factors. This proves the model rather than taking
the product-kernel representability as an additional hypothesis. -/
def tupleKernel_model
    (s : ℕ) (F : Fin s → TorsionQuotient.SubgroupFunctor.RelativeSubgroup A P) (R : ∀ i, (F i).Model)
    (p : Fin s → (A ⟶ A)) [∀ i, IsMonHom (p i)]
    (hsupport : ∀ i, (R i).toGroup ≫ p i = (R i).toGroup)
    (hdisjoint : ∀ i j, i ≠ j → (R j).toGroup ≫ p i = 1) :
    (Construction.tupleKernel s F).Model := by
  induction s with
  | zero => exact trivialRelativeSubgroup_model
  | succ s ih =>
      let Ft := fun i : Fin s => F i.succ
      let Rt := fun i : Fin s => R i.succ
      let pt := fun i : Fin s => p i.succ
      let Q := ih Ft Rt pt (fun i => hsupport i.succ)
        (fun i j hij => hdisjoint i.succ j.succ (fun h => hij (Fin.succ_inj.mp h)))
      have htail : AnnihilatedBy (Construction.tupleKernel s Ft) (p 0) :=
        tupleKernel_annihilated s Ft (p 0) (fun i =>
          (annihilatedBy_iff_model_equation (F i.succ) (R i.succ) (p 0)).mpr
            (hdisjoint 0 i.succ (Fin.succ_ne_zero i).symm))
      exact Product.Construction.relativeKernelProduct_model (F 0) (Construction.tupleKernel s Ft) (R 0) Q (p 0)
        (hsupport 0) ((annihilatedBy_iff_model_equation _ Q _).mp htail)

theorem relativeKernelProduct_baseChange (F G : TorsionQuotient.SubgroupFunctor.RelativeSubgroup A P)
    {Q : Over S} (b : Q ⟶ P) :
    (Product.Construction.relativeKernelProduct F G).baseChange b = Product.Construction.relativeKernelProduct (F.baseChange b) (G.baseChange b) := rfl

theorem tupleKernel_baseChange
    (s : ℕ) (F : Fin s → TorsionQuotient.SubgroupFunctor.RelativeSubgroup A P) {Q : Over S} (b : Q ⟶ P) :
    (Construction.tupleKernel s F).baseChange b = Construction.tupleKernel s (fun i => (F i).baseChange b) := by
  induction s with
  | zero => rfl
  | succ s ih =>
      change (Product.Construction.relativeKernelProduct (F 0) (Construction.tupleKernel s (fun i => F i.succ))).baseChange b = _
      rw [relativeKernelProduct_baseChange, ih]
      rfl

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Kernel.Tuples.Construction
