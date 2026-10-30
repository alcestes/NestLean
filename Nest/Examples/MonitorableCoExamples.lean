import Nest.Examples.Bookreview
import Nest.Examples.Store
import Nest.Examples.Vpn
import Nest.Examples.Firewall
import Nest.Examples.Dns
import Nest.Examples.Auction
import Nest.Examples.Cdn
import Nest.Examples.Sip
import Nest.Examples.Pop3
import Nest.Examples.Game
import Nest.MonitorableCoFin

open Cslib
open Cslib.LTS

/-!
# MonitorableCo examples: session and network co-monitorability.

Proves `MonitorableCo` for every local session type and
`Network.MonitorableCo` for every empty-queue `Net` under `Nest/Examples/`
via `MonitorableCo.of_check` (`by decide`). See `PLAN-MonitorableCo-of_check.md`.
-/

namespace Bookreview

/-- Co-monitorability of `BookClient`. -/
theorem BookClient_mon_co : MonitorableCo BookClient :=
  MonitorableCo.of_check (bfsFuel := 20) (stepFuel := 10) (by decide)

/-- Co-monitorability of `BookInfo`. -/
theorem BookInfo_mon_co : MonitorableCo BookInfo :=
  MonitorableCo.of_check (bfsFuel := 20) (stepFuel := 10) (by decide)

/-- Co-monitorability of `BookReview`. -/
theorem BookReview_mon_co : MonitorableCo BookReview :=
  MonitorableCo.of_check (bfsFuel := 20) (stepFuel := 10) (by decide)

/-- Co-monitorability of `BookDetails`. -/
theorem BookDetails_mon_co : MonitorableCo BookDetails :=
  MonitorableCo.of_check (bfsFuel := 20) (stepFuel := 10) (by decide)

/-- Co-monitorability of `BookRatings`. -/
theorem BookRatings_mon_co : MonitorableCo BookRatings :=
  MonitorableCo.of_check (bfsFuel := 20) (stepFuel := 10) (by decide)

/-- `Net` is coinductively monitorable. -/
theorem Net_monitorable_co : Network.MonitorableCo Net := by
  refine Network.MonitorableCo_of_all_nil Net (by decide) ?_
  intro x hx
  simp only [Net, List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact BookClient_mon_co
  · exact BookInfo_mon_co
  · exact BookReview_mon_co
  · exact BookDetails_mon_co
  · exact BookRatings_mon_co

end Bookreview

namespace Store

/-- Co-monitorability of `Client`. -/
theorem Client_mon_co : MonitorableCo Client :=
  MonitorableCo.of_check (bfsFuel := 30) (stepFuel := 15) (by decide)

/-- Co-monitorability of `HTTP`. -/
theorem HTTP_mon_co : MonitorableCo HTTP :=
  MonitorableCo.of_check (bfsFuel := 30) (stepFuel := 15) (by decide)

/-- Co-monitorability of `Inventory`. -/
theorem Inventory_mon_co : MonitorableCo Inventory :=
  MonitorableCo.of_check (bfsFuel := 30) (stepFuel := 15) (by decide)

/-- Co-monitorability of `Payment`. -/
theorem Payment_mon_co : MonitorableCo Payment :=
  MonitorableCo.of_check (bfsFuel := 30) (stepFuel := 15) (by decide)

/-- Co-monitorability of `Shipping`. -/
theorem Shipping_mon_co : MonitorableCo Shipping :=
  MonitorableCo.of_check (bfsFuel := 30) (stepFuel := 15) (by decide)

/-- Co-monitorability of `Bank`. -/
theorem Bank_mon_co : MonitorableCo Bank :=
  MonitorableCo.of_check (bfsFuel := 30) (stepFuel := 15) (by decide)

/-- Co-monitorability of `Email`. -/
theorem Email_mon_co : MonitorableCo Email :=
  MonitorableCo.of_check (bfsFuel := 30) (stepFuel := 15) (by decide)

/-- `Net` is coinductively monitorable. -/
theorem Net_monitorable_co : Network.MonitorableCo Net := by
  refine Network.MonitorableCo_of_all_nil Net (by decide) ?_
  intro x hx
  simp only [Net, List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Client_mon_co
  · exact HTTP_mon_co
  · exact Inventory_mon_co
  · exact Payment_mon_co
  · exact Shipping_mon_co
  · exact Bank_mon_co
  · exact Email_mon_co

end Store

namespace Vpn

/-- Co-monitorability of `Auth`. -/
theorem Auth_mon_co : MonitorableCo Auth :=
  MonitorableCo.of_check (bfsFuel := 40) (stepFuel := 15) (by decide)

/-- Co-monitorability of `ClientA`. -/
theorem ClientA_mon_co : MonitorableCo ClientA :=
  MonitorableCo.of_check (bfsFuel := 40) (stepFuel := 15) (by decide)

/-- Co-monitorability of `ClientB`. -/
theorem ClientB_mon_co : MonitorableCo ClientB :=
  MonitorableCo.of_check (bfsFuel := 40) (stepFuel := 15) (by decide)

/-- Co-monitorability of `ClientC`. -/
theorem ClientC_mon_co : MonitorableCo ClientC :=
  MonitorableCo.of_check (bfsFuel := 40) (stepFuel := 15) (by decide)

/-- `Net` is coinductively monitorable. -/
theorem Net_monitorable_co : Network.MonitorableCo Net := by
  refine Network.MonitorableCo_of_all_nil Net (by decide) ?_
  intro x hx
  simp only [Net, List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact Auth_mon_co
  · exact ClientA_mon_co
  · exact ClientB_mon_co
  · exact ClientC_mon_co

end Vpn

namespace Firewall

/-- Co-monitorability of `ClientInt`. -/
theorem ClientInt_mon_co : MonitorableCo ClientInt :=
  MonitorableCo.of_check (bfsFuel := 20) (stepFuel := 10) (by decide)

/-- Co-monitorability of `ClientExt`. -/
theorem ClientExt_mon_co : MonitorableCo ClientExt :=
  MonitorableCo.of_check (bfsFuel := 20) (stepFuel := 10) (by decide)

/-- `Net` is coinductively monitorable. -/
theorem Net_monitorable_co : Network.MonitorableCo Net := by
  refine Network.MonitorableCo_of_all_nil Net (by decide) ?_
  intro x hx
  simp only [Net, List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl
  · exact ClientInt_mon_co
  · exact ClientExt_mon_co

end Firewall

namespace Dns

/-- Co-monitorability of `DNSClient`. -/
theorem DNSClient_mon_co : MonitorableCo DNSClient :=
  MonitorableCo.of_check (bfsFuel := 20) (stepFuel := 10) (by decide)

/-- Co-monitorability of `LocalDNS`. -/
theorem LocalDNS_mon_co : MonitorableCo LocalDNS :=
  MonitorableCo.of_check (bfsFuel := 20) (stepFuel := 10) (by decide)

/-- Co-monitorability of `RootDNS`. -/
theorem RootDNS_mon_co : MonitorableCo RootDNS :=
  MonitorableCo.of_check (bfsFuel := 20) (stepFuel := 10) (by decide)

/-- Co-monitorability of `TLDDNS`. -/
theorem TLDDNS_mon_co : MonitorableCo TLDDNS :=
  MonitorableCo.of_check (bfsFuel := 20) (stepFuel := 10) (by decide)

/-- Co-monitorability of `AuthDNS`. -/
theorem AuthDNS_mon_co : MonitorableCo AuthDNS :=
  MonitorableCo.of_check (bfsFuel := 20) (stepFuel := 10) (by decide)

/-- `Net` is coinductively monitorable. -/
theorem Net_monitorable_co : Network.MonitorableCo Net := by
  refine Network.MonitorableCo_of_all_nil Net (by decide) ?_
  intro x hx
  simp only [Net, List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact DNSClient_mon_co
  · exact LocalDNS_mon_co
  · exact RootDNS_mon_co
  · exact TLDDNS_mon_co
  · exact AuthDNS_mon_co

end Dns

namespace Auction

/-- Co-monitorability of `Auction`. -/
theorem Auction_mon_co : MonitorableCo Auction :=
  MonitorableCo.of_check (bfsFuel := 40) (stepFuel := 15) (by decide)

/-- Co-monitorability of `BuyerA`. -/
theorem BuyerA_mon_co : MonitorableCo BuyerA :=
  MonitorableCo.of_check (bfsFuel := 40) (stepFuel := 15) (by decide)

/-- Co-monitorability of `BuyerB`. -/
theorem BuyerB_mon_co : MonitorableCo BuyerB :=
  MonitorableCo.of_check (bfsFuel := 40) (stepFuel := 15) (by decide)

/-- `Net` is coinductively monitorable. -/
theorem Net_monitorable_co : Network.MonitorableCo Net := by
  refine Network.MonitorableCo_of_all_nil Net (by decide) ?_
  intro x hx
  simp only [Net, List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact Auction_mon_co
  · exact BuyerA_mon_co
  · exact BuyerB_mon_co

end Auction

namespace Cdn

/-- Co-monitorability of `User`. -/
theorem User_mon_co : MonitorableCo User :=
  MonitorableCo.of_check (bfsFuel := 20) (stepFuel := 10) (by decide)

/-- Co-monitorability of `LocalDNS`. -/
theorem LocalDNS_mon_co : MonitorableCo LocalDNS :=
  MonitorableCo.of_check (bfsFuel := 20) (stepFuel := 10) (by decide)

/-- Co-monitorability of `IntAuthDNS`. -/
theorem IntAuthDNS_mon_co : MonitorableCo IntAuthDNS :=
  MonitorableCo.of_check (bfsFuel := 20) (stepFuel := 10) (by decide)

/-- Co-monitorability of `ExtAuthDNS`. -/
theorem ExtAuthDNS_mon_co : MonitorableCo ExtAuthDNS :=
  MonitorableCo.of_check (bfsFuel := 20) (stepFuel := 10) (by decide)

/-- `Net` is coinductively monitorable. -/
theorem Net_monitorable_co : Network.MonitorableCo Net := by
  refine Network.MonitorableCo_of_all_nil Net (by decide) ?_
  intro x hx
  simp only [Net, List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact User_mon_co
  · exact LocalDNS_mon_co
  · exact IntAuthDNS_mon_co
  · exact ExtAuthDNS_mon_co

end Cdn

namespace Sip

/-- Co-monitorability of `SIPClientA`. -/
theorem SIPClientA_mon_co : MonitorableCo SIPClientA :=
  MonitorableCo.of_check (bfsFuel := 20) (stepFuel := 10) (by decide)

/-- Co-monitorability of `SIPClientB`. -/
theorem SIPClientB_mon_co : MonitorableCo SIPClientB :=
  MonitorableCo.of_check (bfsFuel := 20) (stepFuel := 10) (by decide)

/-- Co-monitorability of `SIPProxy`. -/
theorem SIPProxy_mon_co : MonitorableCo SIPProxy :=
  MonitorableCo.of_check (bfsFuel := 20) (stepFuel := 10) (by decide)

/-- `Net` is coinductively monitorable. -/
theorem Net_monitorable_co : Network.MonitorableCo Net := by
  refine Network.MonitorableCo_of_all_nil Net (by decide) ?_
  intro x hx
  simp only [Net, List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact SIPClientA_mon_co
  · exact SIPClientB_mon_co
  · exact SIPProxy_mon_co

end Sip

namespace Pop3

/-- Co-monitorability of `POPClient`. -/
theorem POPClient_mon_co : MonitorableCo POPClient :=
  MonitorableCo.of_check (bfsFuel := 30) (stepFuel := 15) (by decide)

/-- Co-monitorability of `POPServer`. -/
theorem POPServer_mon_co : MonitorableCo POPServer :=
  MonitorableCo.of_check (bfsFuel := 30) (stepFuel := 15) (by decide)

/-- `Net` is coinductively monitorable. -/
theorem Net_monitorable_co : Network.MonitorableCo Net := by
  refine Network.MonitorableCo_of_all_nil Net (by decide) ?_
  intro x hx
  simp only [Net, List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl
  · exact POPClient_mon_co
  · exact POPServer_mon_co

end Pop3

namespace Game

/-- Co-monitorability of `Coordinator`. -/
theorem Coordinator_mon_co : MonitorableCo Coordinator :=
  MonitorableCo.of_check (bfsFuel := 30) (stepFuel := 15) (by decide)

/-- Co-monitorability of `GameServer`. -/
theorem GameServer_mon_co : MonitorableCo GameServer :=
  MonitorableCo.of_check (bfsFuel := 30) (stepFuel := 15) (by decide)

/-- Co-monitorability of `Player`. -/
theorem Player_mon_co : MonitorableCo Player :=
  MonitorableCo.of_check (bfsFuel := 30) (stepFuel := 15) (by decide)

/-- `Net` is coinductively monitorable. -/
theorem Net_monitorable_co : Network.MonitorableCo Net := by
  refine Network.MonitorableCo_of_all_nil Net (by decide) ?_
  intro x hx
  simp only [Net, List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact Coordinator_mon_co
  · exact GameServer_mon_co
  · exact Player_mon_co
  · exact Player_mon_co

end Game
