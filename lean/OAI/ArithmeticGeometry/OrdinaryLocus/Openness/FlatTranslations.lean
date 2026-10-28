import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.BaseChange
import Mathlib.AlgebraicGeometry.Group.Smooth

/-! # Flat Translations -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FlatTranslations.Construction

noncomputable section

/-! Transporting flatness by group translations in the Openness development. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

/-- A commuting pair of automorphisms transports a source open on which
a morphism is flat. -/
theorem flat_preimage_of_commuting_isos
    {X Y : Scheme} (f : X ⟶ Y) (α : X ≅ X) (β : Y ≅ Y)
    (hcomm : α.hom ≫ f = f ≫ β.hom)
    (U : X.Opens) [Flat (U.ι ≫ f)] :
    Flat ((α.hom ⁻¹ᵁ U).ι ≫ f) := by
  have hflat : Flat ((α.hom ∣_ U) ≫ (U.ι ≫ f)) := inferInstance
  have heq : (α.hom ∣_ U) ≫ (U.ι ≫ f) =
      ((α.hom ⁻¹ᵁ U).ι ≫ f) ≫ β.hom := by
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc, hcomm, Category.assoc]
  rw [heq] at hflat
  have : Flat ((((α.hom ⁻¹ᵁ U).ι ≫ f) ≫ β.hom) ≫ β.inv) := inferInstance
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using this

/-- If commuting source/target automorphisms act transitively on closed
source points, flatness on one nonempty source open implies global flatness. -/
theorem flat_of_transitive_automorphisms
    {X Y : Scheme} [JacobsonSpace X] (f : X ⟶ Y)
    (htrans : ∀ (x y : X), IsClosed {x} → IsClosed {y} →
      ∃ (α : X ≅ X) (β : Y ≅ Y), α.hom x = y ∧ α.hom ≫ f = f ≫ β.hom)
    (U : X.Opens) (hU : (U : Set X).Nonempty) [Flat (U.ι ≫ f)] :
    Flat f := by
  have : IsZariskiLocalAtSource @AlgebraicGeometry.Flat :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := @RingHom.Flat)
  let I := {V : X.Opens // Flat (V.ι ≫ f)}
  let V : I → X.Opens := Subtype.val
  have htop : iSup V = ⊤ := by
    by_contra hne
    have hex : ∃ x : X, x ∉ iSup V := by
      by_contra! h
      apply hne
      exact le_antisymm le_top (fun x _ => h x)
    obtain ⟨x₀, hx₀⟩ := hex
    obtain ⟨x, hx, hxc⟩ := nonempty_inter_closedPoints
      (Z := ((iSup V : X.Opens) : Set X)ᶜ) ⟨x₀, hx₀⟩
      (iSup V).isOpen.isClosed_compl.isLocallyClosed
    obtain ⟨y, hy, hyc⟩ := nonempty_inter_closedPoints hU U.isOpen.isLocallyClosed
    obtain ⟨α, β, hxy, hcomm⟩ := htrans x y hxc hyc
    let W := α.hom ⁻¹ᵁ U
    have hW : Flat (W.ι ≫ f) := flat_preimage_of_commuting_isos f α β hcomm U
    have hxW : x ∈ W := by
      change α.hom x ∈ U
      rwa [hxy]
    exact hx ((le_iSup V ⟨W, hW⟩) hxW)
  exact IsZariskiLocalAtSource.of_iSup_eq_top
    (P := @AlgebraicGeometry.Flat) (f := f) V htop (fun i => i.prop)

/-- Multiplication by n intertwines translation by b with translation by b^n. -/
theorem multiplication_translation
    {S : Scheme} (A : Over S) [GrpObj A] [IsCommMonObj A]
    (n : ℕ) (b : 𝟙_ (Over S) ⟶ A) :
    (GrpObj.mulRight b).hom ≫ Multiplication.Construction.multiplicationMap A n =
      Multiplication.Construction.multiplicationMap A n ≫ (GrpObj.mulRight (b ^ n)).hom := by
  simp [GrpObj.mulRight, Multiplication.Construction.multiplicationMap, ← Hom.mul_def,
    MonObj.comp_pow, MonObj.comp_mul, mul_pow]

/-- Group translations give commuting automorphisms carrying any closed
source point of multiplication to any other closed source point. -/
theorem multiplication_transitive_automorphisms
    {K : Type*} [Field K] [IsAlgClosed K]
    (A : Over (Spec (.of K))) [GrpObj A] [IsCommMonObj A]
    [LocallyOfFiniteType A.hom] (n : ℕ)
    (x y : A.left) (hx : IsClosed {x}) (hy : IsClosed {y}) :
    ∃ (α : A.left ≅ A.left) (β : A.left ≅ A.left),
      α.hom x = y ∧
      α.hom ≫ (Multiplication.Construction.multiplicationMap A n).left = (Multiplication.Construction.multiplicationMap A n).left ≫ β.hom := by
  let x' : 𝟙_ (Over (Spec (.of K))) ⟶ A :=
    Over.homMk (pointOfClosedPoint A.hom x hx) (pointOfClosedPoint_comp A.hom x hx)
  let y' : 𝟙_ (Over (Spec (.of K))) ⟶ A :=
    Over.homMk (pointOfClosedPoint A.hom y hy) (pointOfClosedPoint_comp A.hom y hy)
  let b := x'⁻¹ * y'
  let α := (Over.forget (Spec (.of K))).mapIso (GrpObj.mulRight b)
  let β := (Over.forget (Spec (.of K))).mapIso (GrpObj.mulRight (b ^ n))
  have hxy : x' ≫ (GrpObj.mulRight b).hom = y' := by
    change x' ≫ (𝟙 A * (toUnit A ≫ b)) = y'
    rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc,
      comp_toUnit, toUnit_unit, Category.id_comp]
    exact mul_inv_cancel_left x' y'
  refine ⟨α, β, ?_, ?_⟩
  · have h : x'.left ≫ α.hom = y'.left := congrArg Over.Hom.left hxy
    have heval :=
      congrArg (fun (z : Spec (.of K) ⟶ A.left) => z (IsLocalRing.closedPoint K)) h
    change α.hom (x'.left (IsLocalRing.closedPoint K)) =
      y'.left (IsLocalRing.closedPoint K) at heval
    have hx' : x'.left (IsLocalRing.closedPoint K) = x :=
      pointOfClosedPoint_apply A.hom x hx _
    have hy' : y'.left (IsLocalRing.closedPoint K) = y :=
      pointOfClosedPoint_apply A.hom y hy _
    rw [hx', hy'] at heval
    exact heval
  · exact congrArg Over.Hom.left (multiplication_translation A n b)

/-- For multiplication on an algebraic group over an algebraically closed
field, one nonempty flat source open suffices for flatness everywhere. -/
theorem flat_multiplication_of_nonempty_flat_open
    {K : Type*} [Field K] [IsAlgClosed K]
    (A : Over (Spec (.of K))) [GrpObj A] [IsCommMonObj A]
    [LocallyOfFiniteType A.hom] (n : ℕ)
    (U : A.left.Opens) (hU : (U : Set A.left).Nonempty)
    [Flat (U.ι ≫ (Multiplication.Construction.multiplicationMap A n).left)] :
    Flat (Multiplication.Construction.multiplicationMap A n).left := by
  have : JacobsonSpace A.left := LocallyOfFiniteType.jacobsonSpace A.hom
  exact flat_of_transitive_automorphisms (Multiplication.Construction.multiplicationMap A n).left
    (multiplication_transitive_automorphisms A n) U hU

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FlatTranslations.Construction
