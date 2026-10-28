import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FiberwiseFlatness
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.GenericFlat
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FiniteEndomorphism
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.SmoothReduced
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.GroupIrreducibleOf
import OAI.AlgebraicGeometry.Picard.Homomorphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Group.Smooth

/-! # Multiplication Flat -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.MultiplicationFlat.Construction.Multiplication

noncomputable section

/-!
# CartierDuality: flatness of finite multiplication

Group translations spread generic flatness across each geometric fiber.
The finite-morphism fiberwise criterion then gives flatness over an
arbitrary base. This proof uses no unfinished statement modules.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

open OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.GenericFlat.Construction.GenericFlatOpen

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
    (GrpObj.mulRight b).hom ≫ ((𝟙 A : A ⟶ A) ^ n) =
      ((𝟙 A : A ⟶ A) ^ n) ≫ (GrpObj.mulRight (b ^ n)).hom := by
  simp [GrpObj.mulRight, ← Hom.mul_def,
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
      α.hom ≫ ((𝟙 A : A ⟶ A) ^ n).left = ((𝟙 A : A ⟶ A) ^ n).left ≫ β.hom := by
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
    [Flat (U.ι ≫ ((𝟙 A : A ⟶ A) ^ n).left)] :
    Flat ((𝟙 A : A ⟶ A) ^ n).left := by
  have : JacobsonSpace A.left := LocallyOfFiniteType.jacobsonSpace A.hom
  exact flat_of_transitive_automorphisms ((𝟙 A : A ⟶ A) ^ n).left
    (multiplication_transitive_automorphisms A n) U hU

/-- An endomorphism over the base of a locally finitely presented
scheme is locally finitely presented. -/
theorem locallyOfFinitePresentation_overEnd
    {S : Scheme.{u}} (A : Over S) [LocallyOfFinitePresentation A.hom] (f : A ⟶ A) :
    LocallyOfFinitePresentation f.left := by
  have h : LocallyOfFinitePresentation (f.left ≫ A.hom) := by
    rw [f.w]
    infer_instance
  exact Picard.Homomorphisms.FinitePresentation.Construction.locallyOfFinitePresentation_of_comp_of_finiteType h inferInstance

/-- Finite multiplication on a smooth proper connected group over an
algebraically closed field is surjective and flat. -/
theorem surjective_flat_power_of_isFinite
    {K : Type u} [Field K] [IsAlgClosed K]
    (A : Over (Spec (.of K))) [GrpObj A] [IsCommMonObj A]
    [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
    (n : ℕ) [IsFinite ((𝟙 A : A ⟶ A) ^ n).left] :
    Surjective ((𝟙 A : A ⟶ A) ^ n).left ∧ Flat ((𝟙 A : A ⟶ A) ^ n).left := by
  have : IrreducibleSpace A.left :=
    Quotients.FiniteDescent.GroupIrreducibleOf.Construction.GroupIrreducible.irreducibleSpace_of_connected_group A
  have : IsReduced A.left := ArithmeticGeometry.OrdinaryLocus.Openness.SmoothReduced.Construction.isReduced_smooth_over_field A.hom
  have : IsIntegral A.left := isIntegral_of_irreducibleSpace_of_isReduced A.left
  have : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  have : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
  have : IsNoetherian A.left := ⟨⟩
  have hs : Surjective ((𝟙 A : A ⟶ A) ^ n).left :=
    ArithmeticGeometry.OrdinaryLocus.Openness.FiniteEndomorphism.Construction.surjective_finite_endomorphism_of_isIntegral ((𝟙 A : A ⟶ A) ^ n).left
  have : LocallyOfFinitePresentation ((𝟙 A : A ⟶ A) ^ n).left :=
    locallyOfFinitePresentation_overEnd A _
  obtain ⟨U, hU, hfU⟩ :=
    GenericFlat.Construction.GenericFlatOpen.exists_nonempty_flat_source_open_of_reduced ((𝟙 A : A ⟶ A) ^ n).left
  have : Flat (U.ι ≫ ((𝟙 A : A ⟶ A) ^ n).left) := hfU
  exact ⟨hs, flat_multiplication_of_nonempty_flat_open A n U hU⟩

/-- Finite multiplication on a smooth proper group with geometrically
connected fibers is flat, with no restriction on the integer. -/
theorem flat_power_of_isFinite
    {S : Scheme.{u}} (A : Over S) [GrpObj A] [IsCommMonObj A]
    [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
    (n : ℕ) [IsFinite ((𝟙 A : A ⟶ A) ^ n).left] :
    Flat ((𝟙 A : A ⟶ A) ^ n).left := by
  have : LocallyOfFinitePresentation ((𝟙 A : A ⟶ A) ^ n).left :=
    locallyOfFinitePresentation_overEnd A _
  apply ArithmeticGeometry.OrdinaryLocus.Openness.FiberwiseFlatness.Construction.flat_finite_of_flat_geometric_baseChanges ((𝟙 A : A ⟶ A) ^ n)
  intro K _ _ t
  let F := Over.pullback t
  let B := F.obj A
  have : Smooth B.hom := by change Smooth (pullback.snd A.hom t); infer_instance
  have : IsProper B.hom := by change IsProper (pullback.snd A.hom t); infer_instance
  have : GeometricallyConnected B.hom := by
    change GeometricallyConnected (pullback.snd A.hom t)
    infer_instance
  have hp : F.map ((𝟙 A : A ⟶ A) ^ n) = (𝟙 B : B ⟶ B) ^ n := by
    exact ((F.homMonoidHom (X := A) (M := A)).map_pow (𝟙 A) n).trans
      (congrArg (fun k => k ^ n) (F.map_id A))
  have hfin : IsFinite (F.map ((𝟙 A : A ⟶ A) ^ n)).left :=
    MorphismProperty.overPullbackMap (P := @IsFinite) t _ inferInstance
  rw [hp] at hfin
  have hf : Flat ((𝟙 B : B ⟶ B) ^ n).left :=
    (surjective_flat_power_of_isFinite B n).2
  change Flat (F.map ((𝟙 A : A ⟶ A) ^ n)).left
  rwa [hp]

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.MultiplicationFlat.Construction.Multiplication
