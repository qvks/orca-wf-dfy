////////////////////CONFIG////////////////////
datatype C = createConfig(heap: Heap, actors: Actors)

//Heap 
datatype Heap = CHeap(objs: map<Addr, map<FId, Addr>>)

//Addrs
type Addr = int
type ObjectAddr = int
type ActorAddr = int 
/* 
datatype Addr = Cons(id: int)
datatype ObjectAddr = Cons(id: int)
datatype ActorAddr = Cons(id: int) 
*/

type Actors = map<ActorAddr, Actor>
//datatype Queue = CQueue(msgs: seq<Msg>)
type Queue = seq<Msg>
datatype Msg = orca(i: Addr, z: int) | app(b: BId, is: seq<ObjectAddr>)
//datatype Msg = orca(i: Addr, z: int) | app(f: Frame) ..alternative: only a frame is passed
//type Actor = (q: Queue, rct: RefCountT, s: State)
datatype Actor = CActor(q: Queue, rct: RefCountT, st: State)
type RefCountT = map<Addr, int>

//Paths 
datatype LP = This | frm(zero: int, x: VarId) | cons(lp: LP, f: FId)
datatype MP = frm(k: int, x: VarId) | cons(mp: MP, f: FId)
datatype SP = This | bsp(b: BId, x: VarId) | cons(sp: SP, f: FId)
datatype Capability = WRITE | READ | TAG

//State 
datatype State = idl | exe(f: Frame) | snd(f': Frame, a: Actor, m: Msg, ws: Workset)
                | mkU(ms: Marks) | trc(ms': Marks) | mkR(ms'': Marks) | cll(ms''': Marks)
datatype Frame = CFrame(BId, map<VarId, Addr>)
type Workset = set<Addr> 
//datatype Marks = CMarks(map<Addr, RU>)
type Marks = map<Addr, RU>
datatype RU = R | U

//IDs
type FId = int 
type BId = int
type ClassId = int
type VarId = int




