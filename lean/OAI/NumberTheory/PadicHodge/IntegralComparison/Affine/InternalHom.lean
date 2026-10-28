import OAI.NumberTheory.PadicHodge.IntegralComparison.SchemeInternalHom
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.CategoryTheory.HomCongr
import Mathlib.CategoryTheory.Linear.Basic

/-! # Internal Hom -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.InternalHom

noncomputable section

/-! Sections of the genuine internal Hom on an affine spectrum are
linear maps between the actual section modules when the source is
quasicoherent. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false

universe u

variable {R : Type u} [CommRing R]
  (M N : (Spec (CommRingCat.of R)).Modules)

abbrev sections := moduleSpecΓFunctor (R := CommRingCat.of R)

def homEquiv [M.IsQuasicoherent] :
    (M ⟶ N) ≃ ((sections.obj M) ⟶ (sections.obj N)) := by
  letI : IsIso (Scheme.Modules.fromTildeΓ (R := CommRingCat.of R) M) :=
    Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent (R := CommRingCat.of R) M
  let e : (tilde.functor (CommRingCat.of R)).obj (sections.obj M) ≅ M :=
    asIso (Scheme.Modules.fromTildeΓ (R := CommRingCat.of R) M)
  exact (Iso.homCongr e.symm (Iso.refl N)).trans
    ((tilde.adjunction (R := CommRingCat.of R)).homEquiv (sections.obj M) N)

theorem homEquiv_apply [M.IsQuasicoherent] (f : M ⟶ N) :
    InternalHom.homEquiv M N f = sections.map f := by
  change (tilde.adjunction (R := CommRingCat.of R)).unit.app (sections.obj M) ≫
    sections.map (Scheme.Modules.fromTildeΓ (R := CommRingCat.of R) M ≫ f ≫ 𝟙 N) = sections.map f
  rw [Category.comp_id, CategoryTheory.Functor.map_comp, ← Category.assoc]
  exact (congrArg (fun t => t ≫ sections.map f)
    ((tilde.adjunction (R := CommRingCat.of R)).right_triangle_components M)).trans
      (Category.id_comp _)

def evaluation : (sections.obj (ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomModule.Construction.sheafHomModule M N)) →ₗ[R]
    (sections.obj M ⟶ sections.obj N) where
  toFun q := sections.map ((SchemeInternalHom.globalSectionsEquiv M N).symm q)
  map_add' q q' := by
    ext m
    rfl
  map_smul' r q := by
    ext m
    let z : Γ(N, ⊤) := q.val.app (op (Over.mk (𝟙 (⊤ : (Spec (CommRingCat.of R)).Opens)))) m
    let a : Γ(Spec (CommRingCat.of R), ⊤) :=
      (Spec (CommRingCat.of R)).presheaf.map (𝟙 (op ⊤)) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r)
    change (Spec (CommRingCat.of R)).presheaf.map (𝟙 (op (⊤ : (Spec (CommRingCat.of R)).Opens))) a • z = a • z
    rw [(Spec (CommRingCat.of R)).presheaf.map_id (op ⊤)]
    rfl

theorem evaluation_bijective [M.IsQuasicoherent] : Function.Bijective (evaluation M N) := by
  have he : (evaluation M N : _ → _) = fun q => InternalHom.homEquiv M N
      ((SchemeInternalHom.globalSectionsEquiv M N).symm q) := by
    funext q
    exact (homEquiv_apply M N _).symm
  rw [he]
  exact (InternalHom.homEquiv M N).bijective.comp (SchemeInternalHom.globalSectionsEquiv M N).symm.bijective

def equiv [M.IsQuasicoherent] : (sections.obj (ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomModule.Construction.sheafHomModule M N)) ≃ₗ[R]
    (sections.obj M ⟶ sections.obj N) :=
  LinearEquiv.ofBijective (evaluation M N) (evaluation_bijective M N)

theorem precomp {M' : (Spec (CommRingCat.of R)).Modules} (f : M ⟶ M')
    (q : sections.obj (ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomModule.Construction.sheafHomModule M' N)) :
    evaluation M N ((sections.map (ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomFunctoriality.Construction.sheafHomMap f (𝟙 N))) q) =
      sections.map f ≫ evaluation M' N q := by
  ext m
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.InternalHom
