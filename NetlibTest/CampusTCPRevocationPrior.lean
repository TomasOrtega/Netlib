import Netlib.Check.CampusTCPStartupTransferCheck
import NetlibTest.CampusTCPRevocationFixture

namespace NetlibTest.CampusTCPRevocationPrior

open Netlib

export Check.CampusTCPStartupTransferCheck (rawReserves CheckedReport checkReport)

abbrev Checked (fixture : CampusTCPRevocationFixture.Fixture) :=
  CheckedReport fixture.base.report fixture.base.config fixture.transferEnd

def check (fixture : CampusTCPRevocationFixture.Fixture) : Except String (Checked fixture) :=
  checkReport fixture.base.report fixture.base.config fixture.transferEnd

end NetlibTest.CampusTCPRevocationPrior
