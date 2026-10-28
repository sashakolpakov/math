import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.Actions
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.EtaleDescentLocal

/-! # Action Descent -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-!
An integral action descends from overlap compatibility on a finite integral
basis. The global maps, group compatibility, and all ring identities are
constructed and proved; none is an input descended-action field.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.Module
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.Functor
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

section Reflection

variable {C D : Type*} [Category* C] [Category* D]
  [MonoidalCategory C] [MonoidalCategory D]
  (F : C ⥤ D) [F.Monoidal] [F.Faithful]
  {X Y : C} [MonObj X] [MonObj Y]

/-- A faithful strong monoidal functor reflects the two group-homomorphism
identities on an actual morphism. -/
theorem ActionDescent.isMonHom_of_faithful_map (f : X ⟶ Y) [IsMonHom (F.map f)] : IsMonHom f where
  one_hom := by
    apply F.map_injective
    apply (cancel_epi (LaxMonoidal.ε F)).mp
    have h := IsMonHom.one_hom (F.map f)
    change (LaxMonoidal.ε F ≫ F.map MonObj.one) ≫ F.map f =
      LaxMonoidal.ε F ≫ F.map MonObj.one at h
    simpa only [Category.assoc, F.map_comp] using h
  mul_hom := by
    apply F.map_injective
    apply (cancel_epi (LaxMonoidal.μ F X X)).mp
    have h := IsMonHom.mul_hom (F.map f)
    change (LaxMonoidal.μ F X X ≫ F.map MonObj.mul) ≫ F.map f =
      (F.map f ⊗ₘ F.map f) ≫ LaxMonoidal.μ F Y Y ≫ F.map MonObj.mul at h
    rw [LaxMonoidal.μ_natural_assoc] at h
    simpa only [Category.assoc, F.map_comp] using h

end Reflection

variable {S T : Scheme} (u : T ⟶ S)
  [Flat u] [Surjective u] [LocallyOfFinitePresentation u]
  {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)

theorem Finite.Actions.GroupEndRing.pullback_injective : Function.Injective (Finite.Actions.GroupEndRing.pullback A u) := by
  intro f h heq
  apply Finite.Actions.GroupEndRing.ext
  apply (Over.pullback u).map_injective
  exact congrArg (Finite.Actions.GroupEndRing.hom (A.pullback u)) heq

/-- A local group endomorphism descends as a group endomorphism from its
actual overlap equation. -/
theorem ActionDescent.endomorphism_descends_from_overlap (f : Finite.Actions.GroupEndRing (A.pullback u))
    (hf : AbelianModuli.ReferenceFamily.EtaleDescentLocal.EtaleDescent.Compatible u (f.hom (A.pullback u))) :
    ∃! e : Finite.Actions.GroupEndRing A, Finite.Actions.GroupEndRing.pullback A u e = f := by
  obtain ⟨e, he, _⟩ := AbelianModuli.ReferenceFamily.EtaleDescentLocal.EtaleDescent.exists_unique_morphism u
    (f.hom (A.pullback u)) hf
  have : IsMonHom ((Over.pullback u).map e) := by
    rw [he]
    exact inferInstanceAs (IsMonHom (f.hom (A.pullback u)))
  have : IsMonHom e := ActionDescent.isMonHom_of_faithful_map (Over.pullback u) e
  have hg : Finite.Actions.GroupEndRing.pullback A u (Finite.Actions.GroupEndRing.ofHom A e) = f :=
    Finite.Actions.GroupEndRing.ext _ he
  exact ⟨Finite.Actions.GroupEndRing.ofHom A e, hg, fun d hd =>
    Finite.Actions.GroupEndRing.pullback_injective u A (hd.trans hg.symm)⟩

variable (E : Type) [Field E] [NumberField E]

/-- Finitely many overlap equations suffice to construct the entire
descended integral action, with equality to the original local action
after actual base change. -/
theorem ActionDescent.integral_action_descends_from_basis_overlaps
    (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) (A.pullback u))
    (hρ : ∀ i, AbelianModuli.ReferenceFamily.EtaleDescentLocal.EtaleDescent.Compatible u (ρ.map (Finite.Actions.integralActionBasis E i))) :
    ∃! σ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A,
      σ.pullback u = ρ := by
  let b := Finite.Actions.integralActionBasis E
  let r := Finite.Actions.ringHomOfIntegralAction (A.pullback u) ρ
  choose e he hu using fun i => ActionDescent.endomorphism_descends_from_overlap u A (r (b i)) (hρ i)
  let v : Fin (Module.finrank ℤ (NumberField.RingOfIntegers E)) → Finite.Actions.GroupEndRing A := e
  let F := Finite.Actions.GroupEndRing.pullback A u
  have hL : F.toAddMonoidHom.toIntLinearMap.comp (Finite.Actions.basisExtension b v) =
      r.toAddMonoidHom.toIntLinearMap := b.ext fun i => by
    change F (Finite.Actions.basisExtension b v (b i)) = r (b i)
    rw [Finite.Actions.basisExtension_basis]
    exact he i
  have hLx (x : NumberField.RingOfIntegers E) : F (Finite.Actions.basisExtension b v x) = r x :=
    LinearMap.congr_fun hL x
  have hone : Finite.Actions.basisExtension b v 1 = 1 := by
    apply Finite.Actions.GroupEndRing.pullback_injective u A
    exact (hLx 1).trans (r.map_one.trans F.map_one.symm)
  have hmul (i j) : Finite.Actions.basisExtension b v (b i * b j) = v i * v j := by
    apply Finite.Actions.GroupEndRing.pullback_injective u A
    rw [F.map_mul, he i, he j, hLx, r.map_mul]
  let σ := Finite.Actions.integralActionOfRingHom A (Finite.Actions.ringHomOfBasis b v hone hmul)
  have hσ : σ.pullback u = ρ := by
    apply Finite.Actions.integralAction_ext
    intro x
    exact congrArg (Finite.Actions.GroupEndRing.hom (A.pullback u)) (hLx x)
  refine ⟨σ, hσ, ?_⟩
  intro τ hτ
  apply Finite.Actions.integralAction_ext
  intro x
  apply (Over.pullback u).map_injective
  exact (congrArg (fun d => d.map x) hτ).trans
    (congrArg (fun d => d.map x) hσ).symm

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
