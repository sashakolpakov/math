import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CartesianFiberComparison
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CartesianMixedProduct
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarization.FiberComparison

/-! # Cartesian Polarization Fiber Map -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CartesianPolarizationFiberMap

noncomputable section

/-! The polarization biextension maps agree on each native fiber
through the actual recovered product comparison. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarization.FiberComparison

theorem polarizationBiextensionMap_cartesian
    {S Y T : Scheme.{0}} {g h : ℕ} {A : HilbertConstruction.Abelian.Schemes.AbelianScheme g Y} (D : HilbertConstruction.Dual.Data.DualAbelianData A)
    {B : HilbertConstruction.Abelian.Schemes.AbelianScheme h S} (E : HilbertConstruction.Dual.Data.DualAbelianData B) (u : Y ⟶ S)
    (eA : A.scheme ≅ (B.pullback u).scheme)
    (eD : D.abelian.scheme ≅ (E.abelian.pullback u).scheme)
    (p : A.scheme ⟶ D.abelian.scheme) (w : B.scheme ⟶ E.abelian.scheme)
    (hc : eA.hom ≫ (Over.pullback u).map w = p ≫ eD.hom) (s : T ⟶ Y) :
    let a := (CartesianFiberComparison.CartesianFamily.fiberComparison u A B eA s).hom
    (a ⊗ₘ a).left ≫ HilbertConstruction.Polarization.FiberComparison.polarizationBiextensionMap E w (s ≫ u) =
      HilbertConstruction.Polarization.FiberComparison.polarizationBiextensionMap D p s ≫ CartesianMixedProduct.CartesianFamily.mixedMap u eD eA := by
  let X := (A.pullback s).scheme
  let Z := (B.pullback (s ≫ u)).scheme
  let a : X ⟶ Z := (CartesianFiberComparison.CartesianFamily.fiberComparison u A B eA s).hom
  let l := (a ⊗ₘ a).left
  let v := HilbertConstruction.Polarization.FiberComparison.polarizationBiextensionMap E w (s ≫ u)
  let t := HilbertConstruction.Polarization.FiberComparison.polarizationBiextensionMap D p s
  let m := CartesianMixedProduct.CartesianFamily.mixedMap u eD eA
  let qA := CartesianFiberComparison.CartesianFamily.totalMap u A.scheme B.scheme eA
  let qD := CartesianFiberComparison.CartesianFamily.totalMap u D.abelian.scheme E.abelian.scheme eD
  let ga := pullback.fst A.scheme.hom s
  let gb := pullback.fst B.scheme.hom (s ≫ u)
  have ha : a.left ≫ gb = ga ≫ qA := CartesianFiberComparison.CartesianFamily.fiberComparison_projection u A B eA s
  have hq : qA ≫ w.left = p.left ≫ qD :=
    CartesianFiberComparison.CartesianFamily.totalMap_morphism_comparison u A B eA eD p w hc
  have hvf : v ≫ (fst E.abelian.scheme B.scheme).left = (fst Z Z).left ≫ gb ≫ w.left :=
    HilbertConstruction.Polarization.FiberComparison.polarizationBiextensionMap_fst E w (s ≫ u)
  have hvs : v ≫ (snd E.abelian.scheme B.scheme).left = (snd Z Z).left ≫ gb :=
    HilbertConstruction.Polarization.FiberComparison.polarizationBiextensionMap_snd E w (s ≫ u)
  have htf : t ≫ (fst D.abelian.scheme A.scheme).left = (fst X X).left ≫ ga ≫ p.left :=
    HilbertConstruction.Polarization.FiberComparison.polarizationBiextensionMap_fst D p s
  have hts : t ≫ (snd D.abelian.scheme A.scheme).left = (snd X X).left ≫ ga :=
    HilbertConstruction.Polarization.FiberComparison.polarizationBiextensionMap_snd D p s
  have hmf : m ≫ (fst E.abelian.scheme B.scheme).left = (fst D.abelian.scheme A.scheme).left ≫ qD :=
    CartesianMixedProduct.CartesianFamily.mixedMap_fst u eD eA
  have hms : m ≫ (snd E.abelian.scheme B.scheme).left = (snd D.abelian.scheme A.scheme).left ≫ qA :=
    CartesianMixedProduct.CartesianFamily.mixedMap_snd u eD eA
  have hlf : l ≫ (fst Z Z).left = (fst X X).left ≫ a.left := Over.tensorHom_left_fst _ _ a a
  have hls : l ≫ (snd Z Z).left = (snd X X).left ≫ a.left := Over.tensorHom_left_snd _ _ a a
  have hw : a.left ≫ (gb ≫ w.left) = (ga ≫ p.left) ≫ qD :=
    (Category.assoc a.left gb w.left).symm.trans
      ((congrArg (fun f => f ≫ w.left) ha).trans
        ((Category.assoc ga qA w.left).trans
          ((congrArg (fun f => ga ≫ f) hq).trans (Category.assoc ga p.left qD).symm)))
  apply Over.tensorObj_ext
  · change (l ≫ v) ≫ (fst E.abelian.scheme B.scheme).left = (t ≫ m) ≫ (fst E.abelian.scheme B.scheme).left
    calc
      _ = l ≫ ((fst Z Z).left ≫ (gb ≫ w.left)) :=
        (Category.assoc _ _ _).trans (congrArg (fun f => l ≫ f) hvf)
      _ = (l ≫ (fst Z Z).left) ≫ (gb ≫ w.left) := (Category.assoc _ _ _).symm
      _ = ((fst X X).left ≫ a.left) ≫ (gb ≫ w.left) := congrArg (fun f => f ≫ (gb ≫ w.left)) hlf
      _ = (fst X X).left ≫ (a.left ≫ (gb ≫ w.left)) := Category.assoc _ _ _
      _ = (fst X X).left ≫ ((ga ≫ p.left) ≫ qD) := congrArg (fun f => (fst X X).left ≫ f) hw
      _ = ((fst X X).left ≫ (ga ≫ p.left)) ≫ qD := (Category.assoc _ _ _).symm
      _ = (t ≫ (fst D.abelian.scheme A.scheme).left) ≫ qD := congrArg (fun f => f ≫ qD) htf.symm
      _ = t ≫ ((fst D.abelian.scheme A.scheme).left ≫ qD) := Category.assoc _ _ _
      _ = t ≫ (m ≫ (fst E.abelian.scheme B.scheme).left) := congrArg (fun f => t ≫ f) hmf.symm
      _ = _ := (Category.assoc _ _ _).symm
  · change (l ≫ v) ≫ (snd E.abelian.scheme B.scheme).left = (t ≫ m) ≫ (snd E.abelian.scheme B.scheme).left
    calc
      _ = l ≫ ((snd Z Z).left ≫ gb) := (Category.assoc _ _ _).trans (congrArg (fun f => l ≫ f) hvs)
      _ = (l ≫ (snd Z Z).left) ≫ gb := (Category.assoc _ _ _).symm
      _ = ((snd X X).left ≫ a.left) ≫ gb := congrArg (fun f => f ≫ gb) hls
      _ = (snd X X).left ≫ (a.left ≫ gb) := Category.assoc _ _ _
      _ = (snd X X).left ≫ (ga ≫ qA) := congrArg (fun f => (snd X X).left ≫ f) ha
      _ = ((snd X X).left ≫ ga) ≫ qA := (Category.assoc _ _ _).symm
      _ = (t ≫ (snd D.abelian.scheme A.scheme).left) ≫ qA := congrArg (fun f => f ≫ qA) hts.symm
      _ = t ≫ ((snd D.abelian.scheme A.scheme).left ≫ qA) := Category.assoc _ _ _
      _ = t ≫ (m ≫ (snd E.abelian.scheme B.scheme).left) := congrArg (fun f => t ≫ f) hms.symm
      _ = _ := (Category.assoc _ _ _).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CartesianPolarizationFiberMap
