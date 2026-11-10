import PA215.CertifiedContracts
import PA215.Census.C015
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard015Part5
open PA215.Contracts PA215.Census

def original2006 : RawOriginal := C015.records[86]'(by decide)
theorem original_id2006 : original2006.index = 2006 := by decide

def c2006 : Contract := original2006.toContract.get (by decide)
theorem binding2006 : original2006.toContract = some c2006 := rfl

theorem checked2006 : check 4000 c2006 = true := by decide

def original2007 : RawOriginal := C015.records[87]'(by decide)
theorem original_id2007 : original2007.index = 2007 := by decide

def c2007 : Contract := original2007.toContract.get (by decide)
theorem binding2007 : original2007.toContract = some c2007 := rfl

theorem checked2007 : check 4000 c2007 = true := by decide

def original2008 : RawOriginal := C015.records[88]'(by decide)
theorem original_id2008 : original2008.index = 2008 := by decide

def c2008 : Contract := original2008.toContract.get (by decide)
theorem binding2008 : original2008.toContract = some c2008 := rfl

theorem checked2008 : check 4000 c2008 = true := by decide

def original2009 : RawOriginal := C015.records[89]'(by decide)
theorem original_id2009 : original2009.index = 2009 := by decide

def c2009 : Contract := original2009.toContract.get (by decide)
theorem binding2009 : original2009.toContract = some c2009 := rfl

theorem checked2009 : check 4000 c2009 = true := by decide

def original2010 : RawOriginal := C015.records[90]'(by decide)
theorem original_id2010 : original2010.index = 2010 := by decide

def c2010 : Contract := original2010.toContract.get (by decide)
theorem binding2010 : original2010.toContract = some c2010 := rfl

theorem checked2010 : check 4000 c2010 = true := by decide

def original2011 : RawOriginal := C015.records[91]'(by decide)
theorem original_id2011 : original2011.index = 2011 := by decide

def c2011 : Contract := original2011.toContract.get (by decide)
theorem binding2011 : original2011.toContract = some c2011 := rfl

theorem checked2011 : check 4000 c2011 = true := by decide

def original2012 : RawOriginal := C015.records[92]'(by decide)
theorem original_id2012 : original2012.index = 2012 := by decide

def c2012 : Contract := original2012.toContract.get (by decide)
theorem binding2012 : original2012.toContract = some c2012 := rfl

theorem checked2012 : check 4000 c2012 = true := by decide

def original2013 : RawOriginal := C015.records[93]'(by decide)
theorem original_id2013 : original2013.index = 2013 := by decide

def c2013 : Contract := original2013.toContract.get (by decide)
theorem binding2013 : original2013.toContract = some c2013 := rfl

theorem checked2013 : check 4000 c2013 = true := by decide

def original2014 : RawOriginal := C015.records[94]'(by decide)
theorem original_id2014 : original2014.index = 2014 := by decide

def c2014 : Contract := original2014.toContract.get (by decide)
theorem binding2014 : original2014.toContract = some c2014 := rfl

theorem checked2014 : check 4000 c2014 = true := by decide

def original2015 : RawOriginal := C015.records[95]'(by decide)
theorem original_id2015 : original2015.index = 2015 := by decide

def c2015 : Contract := original2015.toContract.get (by decide)
theorem binding2015 : original2015.toContract = some c2015 := rfl

theorem checked2015 : check 4000 c2015 = true := by decide

def original2016 : RawOriginal := C015.records[96]'(by decide)
theorem original_id2016 : original2016.index = 2016 := by decide

def c2016 : Contract := original2016.toContract.get (by decide)
theorem binding2016 : original2016.toContract = some c2016 := rfl

theorem checked2016 : check 4000 c2016 = true := by decide

def original2017 : RawOriginal := C015.records[97]'(by decide)
theorem original_id2017 : original2017.index = 2017 := by decide

def c2017 : Contract := original2017.toContract.get (by decide)
theorem binding2017 : original2017.toContract = some c2017 := rfl

theorem checked2017 : check 4000 c2017 = true := by decide

def original2018 : RawOriginal := C015.records[98]'(by decide)
theorem original_id2018 : original2018.index = 2018 := by decide

def c2018 : Contract := original2018.toContract.get (by decide)
theorem binding2018 : original2018.toContract = some c2018 := rfl

theorem checked2018 : check 4000 c2018 = true := by decide

def original2019 : RawOriginal := C015.records[99]'(by decide)
theorem original_id2019 : original2019.index = 2019 := by decide

def c2019 : Contract := original2019.toContract.get (by decide)
theorem binding2019 : original2019.toContract = some c2019 := rfl

theorem checked2019 : check 4000 c2019 = true := by decide

def original2020 : RawOriginal := C015.records[100]'(by decide)
theorem original_id2020 : original2020.index = 2020 := by decide

def c2020 : Contract := original2020.toContract.get (by decide)
theorem binding2020 : original2020.toContract = some c2020 := rfl

theorem checked2020 : check 4000 c2020 = true := by decide

def original2021 : RawOriginal := C015.records[101]'(by decide)
theorem original_id2021 : original2021.index = 2021 := by decide

def c2021 : Contract := original2021.toContract.get (by decide)
theorem binding2021 : original2021.toContract = some c2021 := rfl

theorem checked2021 : check 4000 c2021 = true := by decide

def records : List Certified := [
  ⟨2006, c2006, 4000, checked2006⟩,
  ⟨2007, c2007, 4000, checked2007⟩,
  ⟨2008, c2008, 4000, checked2008⟩,
  ⟨2009, c2009, 4000, checked2009⟩,
  ⟨2010, c2010, 4000, checked2010⟩,
  ⟨2011, c2011, 4000, checked2011⟩,
  ⟨2012, c2012, 4000, checked2012⟩,
  ⟨2013, c2013, 4000, checked2013⟩,
  ⟨2014, c2014, 4000, checked2014⟩,
  ⟨2015, c2015, 4000, checked2015⟩,
  ⟨2016, c2016, 4000, checked2016⟩,
  ⟨2017, c2017, 4000, checked2017⟩,
  ⟨2018, c2018, 4000, checked2018⟩,
  ⟨2019, c2019, 4000, checked2019⟩,
  ⟨2020, c2020, 4000, checked2020⟩,
  ⟨2021, c2021, 4000, checked2021⟩]

end PA215.ContractShards.Shard015Part5
