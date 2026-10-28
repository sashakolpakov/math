import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Universal.KernelQuotient

/-! # Total Parameters -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.TotalParameters.Construction

noncomputable section

/-!
View the relative subgroup parameter as a scheme over the ground base.
Its points are a source moduli point together with an actual relative
subgroup choice. The source projection is finite etale when the relative
parameter is finite etale.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} (M : Over S) (P : Over M.left)

def totalParameter : Over S := Over.mk (P.hom ≫ M.hom)

def totalParameterSource : totalParameter M P ⟶ M := Over.homMk P.hom

theorem totalParameterSource_finite_etale [IsFinite P.hom] [Etale P.hom] :
    IsFinite (totalParameterSource M P).left ∧ Etale (totalParameterSource M P).left :=
  ⟨inferInstanceAs (IsFinite P.hom), inferInstanceAs (Etale P.hom)⟩

private def homFactorEquiv
    {C : Type*} [Category C] {X Y : C} (p : Y ⟶ X) (T : C) :
    (T ⟶ Y) ≃ (Σ x : T ⟶ X, { b : T ⟶ Y // b ≫ p = x }) where
  toFun b := ⟨b ≫ p, b, rfl⟩
  invFun z := z.2.val
  left_inv _ := rfl
  right_inv := by
    rintro ⟨x, b, hb⟩
    cases hb
    rfl

private def totalLiftEquiv (T : Over S) (x : T ⟶ M) :
    { b : T ⟶ totalParameter M P // b ≫ totalParameterSource M P = x } ≃
      (Over.mk x.left ⟶ P) where
  toFun b := Over.homMk b.val.left (congrArg (fun f => f.left) b.property)
  invFun b := ⟨Over.homMk b.left (by
    change b.left ≫ (P.hom ≫ M.hom) = T.hom
    rw [← Category.assoc, b.w]
    exact x.w), by
      apply Over.OverMorphism.ext
      exact b.w⟩
  left_inv _ := Subtype.ext (Over.OverMorphism.ext rfl)
  right_inv _ := Over.OverMorphism.ext rfl

variable (F : (Over M.left)ᵒᵖ ⥤ Type (u + 1))

/-- A source point and a subgroup choice over precisely that source. -/
def TotalParameterPoint (T : Over S) :=
  Σ x : T ⟶ M, F.obj (.op (Over.mk x.left))

/-- The relative classification gives exactly the required pairs of
moduli points and subgroup choices on all ground-base test schemes. -/
def totalParameterPointEquiv (repr : F.RepresentableBy P) (T : Over S) :
    (T ⟶ totalParameter M P) ≃ TotalParameterPoint M F T :=
  (homFactorEquiv (totalParameterSource M P) T).trans
    (Equiv.sigmaCongrRight (fun x => (totalLiftEquiv M P T x).trans repr.homEquiv))

/-- Restricting the source-and-choice classification to a fixed source
point gives exactly that point's relative subgroup choices. -/
def totalParameterFiberEquiv (repr : F.RepresentableBy P) (T : Over S) (x : T ⟶ M) :
    { b : T ⟶ totalParameter M P // b ≫ totalParameterSource M P = x } ≃
      F.obj (.op (Over.mk x.left)) :=
  (totalLiftEquiv M P T x).trans repr.homEquiv

def totalParameterFiberLiftEquiv (T : Over S) (x : T ⟶ M) :
    { b : T ⟶ totalParameter M P // b ≫ totalParameterSource M P = x } ≃
      (Over.mk x.left ⟶ P) := totalLiftEquiv M P T x

def totalPointPullback {T U : Over S} (f : U ⟶ T) :
    TotalParameterPoint M F T → TotalParameterPoint M F U := fun z =>
  ⟨f ≫ z.1, F.map (Over.homMk f.left : Over.mk (f ≫ z.1).left ⟶ Over.mk z.1.left).op z.2⟩

set_option backward.isDefEq.respectTransparency false in
theorem totalPointPullback_classification
    (repr : F.RepresentableBy P) {T U : Over S} (f : U ⟶ T)
    (z : TotalParameterPoint M F T) :
    (totalParameterPointEquiv M P F repr U).symm (totalPointPullback M F f z) =
      f ≫ (totalParameterPointEquiv M P F repr T).symm z := by
  apply Over.OverMorphism.ext
  change (repr.homEquiv.symm
      (F.map (Over.homMk f.left : Over.mk (f ≫ z.1).left ⟶ Over.mk z.1.left).op z.2)).left =
    f.left ≫ (repr.homEquiv.symm z.2).left
  have h := repr.homEquiv_comp
    (Over.homMk f.left : Over.mk (f ≫ z.1).left ⟶ Over.mk z.1.left)
    (repr.homEquiv.symm z.2)
  rw [Equiv.apply_symm_apply] at h
  exact congrArg (fun a => a.left)
    ((repr.homEquiv.symm_apply_eq).mpr h.symm)

/-- The maps are the intrinsic pullbacks of source points and choices.
The proved classification is used only to verify the functor laws. -/
def totalParameterFunctor (repr : F.RepresentableBy P) :
    (Over S)ᵒᵖ ⥤ Type (u + 1) where
  obj T := TotalParameterPoint M F T.unop
  map f := ↾(totalPointPullback M F f.unop)
  map_id T := by
    ext z
    apply (totalParameterPointEquiv M P F repr T.unop).symm.injective
    change (totalParameterPointEquiv M P F repr T.unop).symm
      (totalPointPullback M F (𝟙 T.unop) z) = _
    rw [totalPointPullback_classification]
    exact Category.id_comp _
  map_comp f g := by
    ext z
    apply (totalParameterPointEquiv M P F repr _).symm.injective
    change (totalParameterPointEquiv M P F repr _).symm
      (totalPointPullback M F (g.unop ≫ f.unop) z) =
      (totalParameterPointEquiv M P F repr _).symm
        (totalPointPullback M F g.unop (totalPointPullback M F f.unop z))
    simp only [totalPointPullback_classification, Category.assoc]

/-- The scheme over the ground base represents precisely the source-and-
choice functor, with no additional representability assumption. -/
def totalParameters_representable (repr : F.RepresentableBy P) :
    (totalParameterFunctor M P F repr).RepresentableBy (totalParameter M P) where
  homEquiv := totalParameterPointEquiv M P F repr _
  homEquiv_comp f g := by
    apply (totalParameterPointEquiv M P F repr _).symm.injective
    change (totalParameterPointEquiv M P F repr _).symm
      (totalParameterPointEquiv M P F repr _ (f ≫ g)) =
      (totalParameterPointEquiv M P F repr _).symm
        (totalPointPullback M F f (totalParameterPointEquiv M P F repr _ g))
    rw [totalPointPullback_classification, Equiv.symm_apply_apply, Equiv.symm_apply_apply]

/-- Forget the chosen subgroups, retaining the source point. -/
def totalParameterForget (repr : F.RepresentableBy P) :
    totalParameterFunctor M P F repr ⟶ uliftYoneda.{u + 1}.obj M where
  app _ := ↾fun z => ULift.up z.1
  naturality _ _ _ := rfl

theorem totalParameter_source_compatibility (repr : F.RepresentableBy P)
    (T : Over S) (b : T ⟶ totalParameter M P) :
    (totalParameterPointEquiv M P F repr T b).1 = b ≫ totalParameterSource M P := rfl

/-- Changing the proof of relative representability does not change the
total functor: its points and pullbacks are defined independently. -/
theorem totalParameterFunctor_independent (repr : F.RepresentableBy P)
    (Q : Over M.left) (reprQ : F.RepresentableBy Q) :
    totalParameterFunctor M P F repr = totalParameterFunctor M Q F reprQ := rfl

def totalParameterIso (repr : F.RepresentableBy P) :
    uliftYoneda.{u + 1}.obj (totalParameter M P) ≅ totalParameterFunctor M P F repr :=
  Functor.RepresentableBy.equivUliftYonedaIso _ _ (totalParameters_representable M P F repr)

/-- The representing natural isomorphism commutes with the source map,
as a natural-transformation identity over the ground base. -/
theorem totalParameterIso_forget (repr : F.RepresentableBy P) :
    (totalParameterIso M P F repr).hom ≫ totalParameterForget M P F repr =
      uliftYoneda.{u + 1}.map (totalParameterSource M P) := by
  ext T b
  rfl

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.TotalParameters.Construction
