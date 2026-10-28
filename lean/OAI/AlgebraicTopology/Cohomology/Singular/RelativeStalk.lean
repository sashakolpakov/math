import OAI.AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport
import OAI.AlgebraicTopology.Cohomology.Singular.SheafQuasiIso

/-! # Relative Stalk -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.RelativeStalk

noncomputable section

/-!
# Relative singular cohomology and actual stalks

The actual relative-cochain presheaf has section complex `C⁎(U, U ∩ A)`.
Exactness of filtered module colimits identifies the cohomology of its stalk
with the filtered colimit of these genuine relative cohomology groups. The
comparison is characterized on every actual germ, including after
sheafification. This file makes no identification with the kernel of a
direct-image restriction of sheaves.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.TopologicalSpace
open _root_.TopCat.Presheaf

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {R : Type} [Ring R]
  (M : ModuleCat.{0} R) (X : TopCat.{0}) (A : Set X)

/-- The filtered diagram consists of the actual groups `Hⁿ(U, U ∩ A)` and
the restriction maps of pairs, indexed by neighborhoods shrinking to `x`. -/
abbrev relativeNeighborhoodCohomology (x : X) (n : ℕ) :
    (OpenNhds x)ᵒᵖ ⥤ ModuleCat.{0} R :=
  (OpenNhds.inclusion x).op ⋙ RelativeOpenSupport.relativeCohomologyPresheaf M X A n

/-- Cohomology of the genuine relative-cochain stalk is the filtered
colimit of the actual relative cohomology groups of neighborhoods. -/
def relativeStalkCohomologyIso (x : X) (n : ℕ) :
    (Stalk.stalkCochainComplex (RelativeOpenSupport.relativePresheafComplex M X A) x).homology n ≅
      colimit (relativeNeighborhoodCohomology M X A x n) :=
  Stalk.stalkCohomologyIso (RelativeOpenSupport.relativePresheafComplex M X A) x n ≪≫
    (stalkFunctor (ModuleCat.{0} R) x).mapIso (RelativeOpenSupport.relativeCohomologyPresheafIso M X A n).symm

/-- The comparison carries cohomology of the actual cochain germ to the
actual filtered-colimit injection from that neighborhood. -/
@[reassoc]
theorem relativeStalkCohomologyIso_germ
    (U : Opens X) (x : X) (hx : x ∈ U) (n : ℕ) :
    HomologicalComplex.homologyMap
        (Stalk.cochainGerm (RelativeOpenSupport.relativePresheafComplex M X A) U x hx) n ≫
        (relativeStalkCohomologyIso M X A x n).hom =
      colimit.ι (relativeNeighborhoodCohomology M X A x n) (op ⟨U, hx⟩) := by
  change HomologicalComplex.homologyMap _ n ≫
    ((Stalk.stalkCohomologyIso (RelativeOpenSupport.relativePresheafComplex M X A) x n).hom ≫
      (stalkFunctor (ModuleCat.{0} R) x).map (RelativeOpenSupport.relativeCohomologyPresheafIso M X A n).inv) = _
  rw [← Category.assoc, Stalk.cochainGerm_homology, Category.assoc,
    stalkFunctor_map_germ, ← Category.assoc]
  change (Stalk.openCohomologyIso (RelativeOpenSupport.relativePresheafComplex M X A) U n).hom ≫
    (Stalk.openCohomologyIso (RelativeOpenSupport.relativePresheafComplex M X A) U n).inv ≫ _ = _
  rw [Iso.hom_inv_id_assoc]
  rfl

/-- The true germ map from relative cochains on an open neighborhood to
the stalk of the sheafified relative-cochain complex. -/
def relativeSheafCochainGerm (U : Opens X) (x : X) (hx : x ∈ U) :
    RelativeSequence.relativeSingularCochains M (TopCat.of U) (RelativeOpenSupport.relativeOpenSubspace A U) ⟶
      SheafQuasiIso.sheafStalkCochainComplex
        (SheafQuasiIso.sheafifiedCochainComplex (RelativeOpenSupport.relativePresheafComplex M X A)) x :=
  Stalk.cochainGerm (RelativeOpenSupport.relativePresheafComplex M X A) U x hx ≫
    (SheafQuasiIso.sheafificationStalkComplexIso (RelativeOpenSupport.relativePresheafComplex M X A) x).hom

/-- The sheafified relative complex has the same filtered-colimit
cohomology at every actual stalk. -/
def relativeSheafStalkCohomologyIso (x : X) (n : ℕ) :
    (SheafQuasiIso.sheafStalkCochainComplex
      (SheafQuasiIso.sheafifiedCochainComplex (RelativeOpenSupport.relativePresheafComplex M X A)) x).homology n ≅
      colimit (relativeNeighborhoodCohomology M X A x n) :=
  HomologicalComplex.homologyMapIso
      (SheafQuasiIso.sheafificationStalkComplexIso (RelativeOpenSupport.relativePresheafComplex M X A) x).symm n ≪≫
    relativeStalkCohomologyIso M X A x n

/-- The sheafified comparison is still the one induced by actual germs. -/
@[reassoc]
theorem relativeSheafStalkCohomologyIso_germ
    (U : Opens X) (x : X) (hx : x ∈ U) (n : ℕ) :
    HomologicalComplex.homologyMap (relativeSheafCochainGerm M X A U x hx) n ≫
        (relativeSheafStalkCohomologyIso M X A x n).hom =
      colimit.ι (relativeNeighborhoodCohomology M X A x n) (op ⟨U, hx⟩) := by
  let g := Stalk.cochainGerm (RelativeOpenSupport.relativePresheafComplex M X A) U x hx
  let e : Stalk.stalkCochainComplex (RelativeOpenSupport.relativePresheafComplex M X A) x ≅
      SheafQuasiIso.sheafStalkCochainComplex
        (SheafQuasiIso.sheafifiedCochainComplex (RelativeOpenSupport.relativePresheafComplex M X A)) x :=
    SheafQuasiIso.sheafificationStalkComplexIso (RelativeOpenSupport.relativePresheafComplex M X A) x
  let h := HomologicalComplex.homologyMapIso e n
  let r := (relativeStalkCohomologyIso M X A x n).hom
  change HomologicalComplex.homologyMap (g ≫ e.hom) n ≫ (h.inv ≫ r) = _
  calc
    _ = (HomologicalComplex.homologyMap g n ≫ h.hom) ≫ (h.inv ≫ r) :=
      congrArg (fun f => f ≫ (h.inv ≫ r)) (HomologicalComplex.homologyMap_comp g e.hom n)
    _ = HomologicalComplex.homologyMap g n ≫ (h.hom ≫ h.inv ≫ r) :=
      Category.assoc _ _ _
    _ = HomologicalComplex.homologyMap g n ≫ r :=
      congrArg (fun f => HomologicalComplex.homologyMap g n ≫ f) (h.hom_inv_id_assoc r)
    _ = _ := relativeStalkCohomologyIso_germ M X A U x hx n

/-- Restriction along an actual open inclusion does not change the germ
of a relative cochain in the sheafified relative complex. -/
@[reassoc]
theorem relativeSheafCochainGerm_restrict {U V : Opens X} (i : V ⟶ U)
    (x : X) (hx : x ∈ V) :
    (RelativeOpenSupport.relativeCochainPresheaf M X A).map i.op ≫
        relativeSheafCochainGerm M X A V x hx =
      relativeSheafCochainGerm M X A U x (i.le hx) := by
  apply HomologicalComplex.Hom.ext
  funext n
  change (RelativeOpenSupport.relativeCochainDegreePresheaf M X A n).map i.op ≫
      ((RelativeOpenSupport.relativeCochainDegreePresheaf M X A n).germ V x hx ≫
        (SheafQuasiIso.sheafificationStalkComplexIso (RelativeOpenSupport.relativePresheafComplex M X A) x).hom.f n) =
    (RelativeOpenSupport.relativeCochainDegreePresheaf M X A n).germ U x (i.le hx) ≫
      (SheafQuasiIso.sheafificationStalkComplexIso (RelativeOpenSupport.relativePresheafComplex M X A) x).hom.f n
  rw [← Category.assoc, germ_res]

/-- Exactness of the sheafified relative stalk can be checked on the actual
filtered colimit of neighborhood relative cohomology groups. -/
theorem relativeSheafStalk_exactAt_iff (x : X) (n : ℕ) :
    (SheafQuasiIso.sheafStalkCochainComplex
      (SheafQuasiIso.sheafifiedCochainComplex (RelativeOpenSupport.relativePresheafComplex M X A)) x).ExactAt n ↔
      IsZero (colimit (relativeNeighborhoodCohomology M X A x n)) := by
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact ⟨fun h => h.of_iso (relativeSheafStalkCohomologyIso M X A x n).symm,
    fun h => h.of_iso (relativeSheafStalkCohomologyIso M X A x n)⟩

end

end OAI.AlgebraicTopology.Cohomology.Singular.RelativeStalk
