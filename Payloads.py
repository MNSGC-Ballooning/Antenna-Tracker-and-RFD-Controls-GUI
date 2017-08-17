import PyQt4
import time
import datetime
from datetime import *
from BalloonUpdate import *				# Class to hold balloon info
from MapHTML import *


class Payload:
	""" 
	A class to associate a payload's name with its messages and GPS updates, 
	as well as with its associated browsers in the main GUI
	"""
	
	def __init__(self, name, messageBrowser, gpsBrowser, checkbox, mainWindow):
		self.name = name
		self.mainWindow = mainWindow
		self.checkbox = checkbox
		self.gpsUpdates = []
		self.locations = []
		self.messages = []
		self.newMessages = []
		self.newGPSUpdates = []
		self.messageBrowser = messageBrowser
		self.gpsBrowser = gpsBrowser
		self.map = False
		self.newLocation = False
		self.lat = 0.00
		self.lon = 0.00
		self.alt = 0.00
		
		self.mainWindow.payloadNewLocation.connect(self.mainWindow.updateBalloonLocation)

	def getName(self):		# Returns the payload name
		return self.name
		
	def getCheckbox(self):
		return self.checkbox

	def addMessage(self,msg):			# Determines if a message is actually a GPS update, sorts it appropriately
		temp = PayloadMessage(msg)
		msg = temp.getMessage()
		if len(temp.getMessage().split(',')) == 5:		# GPS Updates are always comma separated with a length of 5
			msg = msg.replace('!','')
			self.gpsUpdates.append(temp)
			self.newGPSUpdates.append(temp)
			self.time = temp.getMessage().split(',')[0]
			seconds = int(self.time.split(':')[0])*3600 + int(self.time.split(':')[1])*60 + int(self.time.split(':')[2])
			self.lat = float(msg.split(',')[1])
			self.lon = float(msg.split(',')[2])
			self.alt = float(msg.split(',')[3])*3.2808
			self.sat = float(msg.split(',')[4])
			self.newLocation = True
			
			#Create new location object
			try:
				newLocation = BalloonUpdate(self.time,seconds,self.lat,self.lon,self.alt,"Payload: "+str(self.name),self.mainWindow.groundLat,self.mainWindow.groundLon,self.mainWindow.groundAlt)
				self.locations.append(newLocation)
			except:
				print("Error creating a new balloon location object from Payload Data")

			try:
				self.mainWindow.payloadNewLocation.emit((newLocation,self))
			except Exception, e:
				print(str(e))
		else:
			self.messages.append(temp)
			self.newMessages.append(temp)
		return 1

	def addWebview(self, webview):
		self.webview = webview
		self.map = True
		
	def updateMap(self):
		self.webview.addPoint(self.locations[-1].getLat(),self.locations[-1].getLon())
		self.newLocation = False
		
	def hasMap(self):
		return self.map
		
	def inNewLocation(self):
		return self.newLocation
		
	def getGPSUpdates(self):			# Returns the list of GPS Updates
		return self.gpsUpdates

	def getMessages(self):				# Returns the list of Messages
		return self.messages

	def getNewMessages(self):			# Returns a list of messages received since the last time this function was called
		temp = self.newMessages
		self.newMessages = []
		return temp
		
	def getNewGPSUpdates(self):			# Returns a list of GPS updates received since the last time this function was called
		temp = self.newGPSUpdates
		self.newGPSUpdates = []
		return temp
		
	def getMessageBrowser(self):		# Returns the message text browser associated with this payload
		return self.messageBrowser
		
	def getGPSBrowser(self):			# Returns the GPS text browser associated with this payload
		return self.gpsBrowser
		
	def isTracking(self):
		return self.checkbox.isChecked()

class PayloadMessage:
	"""
	A class to manage message received from payloads in flight.
	Holds the text of the message, as well as a timestamp for
	when the message was received.
	"""
	
	def __init__(self,msg):			# Create the timestamp and message when this object is created
		self.message = msg
		self.timestamp = datetime.today().strftime('%H:%M:%S')

	def getMessage(self):			# Returns the message
		return self.message

	def getTimestamp(self):			# Returns the timestamp
		return self.timestamp