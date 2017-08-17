/-
author: Ben Sherman

This file introduces a class `network_monad` that extends monad with
operations for communicating over sockets.  These sockets can send and
receive arbitrary length byte sequences as messages.  A socket can
either be specifically created by server given an IP
address and port, or created by an external agent when it sends a
connect message to a port on this server.

IP addresses and ports are modeled as byte sequences and 16-bit
numbers respectively, but can be generally treated as abstract
concepts.

-/

import galois.word
import galois.list.member

universes u v

namespace network

section network_monad

/-- This represents a point in time.

 Our timing model assumes that all computation including sending
 and receiving messages takes zero time.  However, time can pass
 when an agent is blocked waiting for a message. -/
@[reducible]
def time := ℕ

instance time_has_sub : has_sub time := begin unfold time, apply_instance end

-- This defines an IP address.  To be agnostic over the protocol, we
-- just model this as a list of bytes
def ip := list byte

-- A port identifies a public interface to the machine that can
-- accept connections.
def port := word16

-- A remote machine name is given by an ip and port.
def remote_name := ip × port

-- This is the data type returned when trying to receive a message
-- with a timeout with the given list of sockets.
inductive poll_result {socket : Type} (ports : list port) (sockets : list socket) (bound : time) : Type

| timeout {} : poll_result
-- ^ We waited until the elapsed time without receiving a message.

| message {}
: ∀ (elapsed : fin bound) (sock : list.member sockets) (mess : list byte), poll_result
-- ^ We received a message from the socket with the given index.

-- This defines the interface a monad needs to implement to give
-- a semantics to an agent.
class network_monad (m : Type → Type u) extends monad m : Type (u+1) :=
(socket : Type)
-- Create a socket to a machine with the given remote.
(connect : remote_name →  m socket)
-- Send a message on the given socket.
-- This is asynchronous and returns immediately.
(send : socket → list byte → m punit)
-- Stop execution until an event in one of the ports or sockets.
(poll : Π (ports : list port) (sockets : list socket) (bound : time), m (poll_result ports sockets bound))

section

parameter {m : Type → Type u}
parameter [inst : network_monad m]

-- Send a message with the target destination.
def send (dest : inst.socket) (msg : list byte) :=
  network_monad.send dest msg

-- Pause the process to receive messages until one arrives or a timeout occurs/
def poll (ports : list port) (sockets : list inst.socket) (bound : time)
: m (poll_result ports sockets bound) :=
  network_monad.poll ports sockets bound

end

end network_monad

end network
