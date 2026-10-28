import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.FiniteLocallyFreeCoordinates
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Intrinsic Retracts -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.IntrinsicRetracts

noncomputable section

/-!
# CartierDuality: finite locally free native group schemes are closed under direct factors
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

universe u

namespace Construction.Schemes

/-- A retract over the base of a finite scheme is finite over the base. -/
theorem finite_of_over_retract {S : Scheme.{u}} {X Y : Over S} [IsFinite X.hom]
    (i : Y ⟶ X) (r : X ⟶ Y) (h : i ≫ r = 𝟙 Y) : IsFinite Y.hom := by
  let : IsSeparated (r.left ≫ Y.hom) := r.w.symm ▸ inferInstanceAs (IsSeparated X.hom)
  let : IsSeparated r.left := IsSeparated.of_comp r.left Y.hom
  have hi : i.left ≫ r.left = 𝟙 Y.left := congrArg (fun a => a.left) h
  let : IsClosedImmersion (i.left ≫ r.left) := hi.symm ▸ inferInstanceAs (IsClosedImmersion (𝟙 Y.left))
  let : IsClosedImmersion i.left := IsClosedImmersion.of_comp i.left r.left
  exact i.w ▸ inferInstanceAs (IsFinite (i.left ≫ X.hom))

/-- Over an affine base, the coordinate module of a native direct factor
is a direct summand of the original finite projective coordinate module. -/
theorem finiteLocallyFree_of_retract_affine (R : CommRingCat.{u})
    {G H : Grp (Over (Spec R))}
    [IsFinite G.X.hom] [Flat G.X.hom] [LocallyOfFinitePresentation G.X.hom]
    (i : H ⟶ G) (r : G ⟶ H) (h : i ≫ r = 𝟙 H) :
    IsFinite H.X.hom ∧ Flat H.X.hom ∧ LocallyOfFinitePresentation H.X.hom := by
  let : IsFinite H.X.hom := finite_of_over_retract i.hom.hom r.hom.hom
    (congrArg (fun a => a.hom.hom) h)
  obtain ⟨A, hA, hpA, ⟨eA⟩⟩ := FiniteLocallyFreeCoordinates.Construction.exists_finiteProjective_hopfPresentation R G
  let : Module.Finite R A := hA
  let : Module.Projective R A := hpA
  have ha : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom
  obtain ⟨B, ⟨eB⟩⟩ := (essImage_hopfSpec (R := R) (G := H)).mpr ha
  let ig : (hopfSpec R).obj B ⟶ (hopfSpec R).obj (Opposite.op A) := eB.hom ≫ i ≫ eA.inv
  let rg : (hopfSpec R).obj (Opposite.op A) ⟶ (hopfSpec R).obj B := eA.hom ≫ r ≫ eB.inv
  have hig : ig ≫ rg = 𝟙 _ := by
    calc
      ig ≫ rg = eB.hom ≫ (i ≫ r) ≫ eB.inv := by
        simp only [ig, rg, Category.assoc, Iso.inv_hom_id_assoc]
      _ = 𝟙 _ := by rw [h]; simp
  let ia : B ⟶ Opposite.op A := (hopfSpec.fullyFaithful (R := R)).preimage ig
  let ra : Opposite.op A ⟶ B := (hopfSpec.fullyFaithful (R := R)).preimage rg
  have hia : ia ≫ ra = 𝟙 B := by
    apply (hopfSpec R).map_injective
    dsimp only [ia, ra]
    rw [Functor.map_comp, Functor.FullyFaithful.map_preimage,
      Functor.FullyFaithful.map_preimage, (hopfSpec R).map_id]
    exact hig
  let : Module.Projective R B.unop := Module.Projective.of_split
    ra.unop.hom.toLinearMap ia.unop.hom.toLinearMap (by
      apply LinearMap.ext
      intro b
      exact congrArg (fun a : B ⟶ B => a.unop.hom b) hia)
  let e : ((hopfSpec R).obj B).X ≅ H.X := (Grp.forget _).mapIso eB
  let : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget (Spec R)).map e.hom))
  let : IsIso e.inv.left := inferInstanceAs (IsIso ((Over.forget (Spec R)).map e.inv))
  let : IsFinite ((hopfSpec R).obj B).X.hom :=
    e.hom.w ▸ inferInstanceAs (IsFinite (e.hom.left ≫ H.X.hom))
  let : Module.Finite R B.unop :=
    RingHom.finite_algebraMap.mp ((IsFinite.SpecMap_iff (CommRingCat.ofHom (algebraMap R B.unop))).mp
      (inferInstanceAs (IsFinite ((hopfSpec R).obj B).X.hom)))
  obtain ⟨hf, hflat, hfp⟩ := (FiniteLocallyFreeCoordinates.Construction.finiteLocallyFree_spec_iff R B.unop).mpr ⟨inferInstance, inferInstance⟩
  let : IsFinite ((hopfSpec R).obj B).X.hom := hf
  let : Flat ((hopfSpec R).obj B).X.hom := hflat
  let : LocallyOfFinitePresentation ((hopfSpec R).obj B).X.hom := hfp
  rw [← e.inv.w]
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- Native direct factors of finite locally free group schemes are
finite locally free over an arbitrary scheme base. -/
theorem finiteLocallyFree_of_retract {S : Scheme.{u}} {G H : Grp (Over S)}
    [IsFinite G.X.hom] [Flat G.X.hom] [LocallyOfFinitePresentation G.X.hom]
    (i : H ⟶ G) (r : G ⟶ H) (h : i ≫ r = 𝟙 H) :
    IsFinite H.X.hom ∧ Flat H.X.hom ∧ LocallyOfFinitePresentation H.X.hom := by
  have hl : ∀ k, IsFinite (pullback.snd H.X.hom (S.affineCover.f k)) ∧
      Flat (pullback.snd H.X.hom (S.affineCover.f k)) ∧
      LocallyOfFinitePresentation (pullback.snd H.X.hom (S.affineCover.f k)) := by
    intro k
    let f := S.affineCover.f k
    let F := (Over.pullback f).mapGrp
    let G' := F.obj G
    let hfin : IsFinite G'.X.hom := inferInstanceAs (IsFinite (pullback.snd G.X.hom f))
    let hflat : Flat G'.X.hom := inferInstanceAs (Flat (pullback.snd G.X.hom f))
    let hfp : LocallyOfFinitePresentation G'.X.hom :=
      inferInstanceAs (LocallyOfFinitePresentation (pullback.snd G.X.hom f))
    have hh : F.map i ≫ F.map r = 𝟙 (F.obj H) :=
      (F.map_comp i r).symm.trans ((congrArg F.map h).trans (F.map_id H))
    exact @finiteLocallyFree_of_retract_affine _ G' (F.obj H) hfin hflat hfp
      (F.map i) (F.map r) hh
  let : IsZariskiLocalAtTarget (@Flat.{u}) :=
    @HasRingHomProperty.instIsZariskiLocalAtTarget (@Flat.{u}) (@RingHom.Flat) inferInstance
  let : IsZariskiLocalAtTarget (@LocallyOfFinitePresentation.{u}) :=
    @HasRingHomProperty.instIsZariskiLocalAtTarget (@LocallyOfFinitePresentation.{u})
      (@RingHom.FinitePresentation) inferInstance
  exact ⟨finite_of_over_retract i.hom.hom r.hom.hom (congrArg (fun a => a.hom.hom) h),
    (IsZariskiLocalAtTarget.iff_of_openCover (P := @Flat.{u}) S.affineCover).mpr (fun k => (hl k).2.1),
    (IsZariskiLocalAtTarget.iff_of_openCover (P := @LocallyOfFinitePresentation.{u}) S.affineCover).mpr
      (fun k => (hl k).2.2)⟩

end Construction.Schemes

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.IntrinsicRetracts
