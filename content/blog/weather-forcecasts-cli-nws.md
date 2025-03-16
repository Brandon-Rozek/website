---
title: "Weather Forcecasts on the Command-Line with the National Weather Service API"
date: 2025-03-16T15:33:49-04:00
draft: true
tags: []
math: false
medium_enabled: false
---

The United States National Weather Service (NWS) has a [JSON API](https://www.weather.gov/documentation/services-web-api) which provides weather alerts and forecasts for free without having to create an API key[^1]. We'll use this resource to write a small bash script which gives today and tomorrow's weather forecast given a latitude and longitude.

[^1]: In this day and age, it almost feels too good to be true. 

My goal is to have a small bash script which I can run in the terminal to get the forecast information. We'll use [`jq`](https://jqlang.org/) for handling the JSON data.

The NWS API does not provide the forecast directly given a latitude and longitude coordinates. Instead, we need to provide the specific [Weather Forecast Office (WFO)](https://www.weather.gov/srh/nwsoffices) responsible for that area plus their grid definitions for the latitude and longitude coordinate.

Luckily, we can query for that information as well.

```bash 
POINTS=$(curl -Ls "https://api.weather.gov/points/$LAT,$LON")
```

{{< unsafe >}}<details><summary>For 42.7289, -73.6915 it returns:</summary>{{</unsafe >}}

```json
{
    "@context": [
        "https://geojson.org/geojson-ld/geojson-context.jsonld",
        {
            "@version": "1.1",
            "wx": "https://api.weather.gov/ontology#",
            "s": "https://schema.org/",
            "geo": "http://www.opengis.net/ont/geosparql#",
            "unit": "http://codes.wmo.int/common/unit/",
            "@vocab": "https://api.weather.gov/ontology#",
            "geometry": {
                "@id": "s:GeoCoordinates",
                "@type": "geo:wktLiteral"
            },
            "city": "s:addressLocality",
            "state": "s:addressRegion",
            "distance": {
                "@id": "s:Distance",
                "@type": "s:QuantitativeValue"
            },
            "bearing": {
                "@type": "s:QuantitativeValue"
            },
            "value": {
                "@id": "s:value"
            },
            "unitCode": {
                "@id": "s:unitCode",
                "@type": "@id"
            },
            "forecastOffice": {
                "@type": "@id"
            },
            "forecastGridData": {
                "@type": "@id"
            },
            "publicZone": {
                "@type": "@id"
            },
            "county": {
                "@type": "@id"
            }
        }
    ],
    "id": "https://api.weather.gov/points/42.7289,-73.6915",
    "type": "Feature",
    "geometry": {
        "type": "Point",
        "coordinates": [
            -73.6915,
            42.7289
        ]
    },
    "properties": {
        "@id": "https://api.weather.gov/points/42.7289,-73.6915",
        "@type": "wx:Point",
        "cwa": "ALY",
        "forecastOffice": "https://api.weather.gov/offices/ALY",
        "gridId": "ALY",
        "gridX": 74,
        "gridY": 67,
        "forecast": "https://api.weather.gov/gridpoints/ALY/74,67/forecast",
        "forecastHourly": "https://api.weather.gov/gridpoints/ALY/74,67/forecast/hourly",
        "forecastGridData": "https://api.weather.gov/gridpoints/ALY/74,67",
        "observationStations": "https://api.weather.gov/gridpoints/ALY/74,67/stations",
        "relativeLocation": {
            "type": "Feature",
            "geometry": {
                "type": "Point",
                "coordinates": [
                    -73.707011,
                    42.724883
                ]
            },
            "properties": {
                "city": "Watervliet",
                "state": "NY",
                "distance": {
                    "unitCode": "wmoUnit:m",
                    "value": 1343.4228258697
                },
                "bearing": {
                    "unitCode": "wmoUnit:degree_(angle)",
                    "value": 70
                }
            }
        },
        "forecastZone": "https://api.weather.gov/zones/forecast/NYZ053",
        "county": "https://api.weather.gov/zones/county/NYC083",
        "fireWeatherZone": "https://api.weather.gov/zones/fire/NYZ208",
        "timeZone": "America/New_York",
        "radarStation": "KENX"
    }
}
```

{{< unsafe >}}</details><br/>{{</unsafe >}}



That's a lot of output! However, we only need three pieces of information:

- WFO office (ex: "ALY")
- Grid-X (ex: 74)
- Grid-Y (ex: 67)

We can use the following code to store this into variables using `jq`

```bash
OFFICE=$(echo $POINTS | jq -r .properties.gridId)
X=$(echo $POINTS | jq .properties.gridX)
Y=$(echo $POINTS | jq .properties.gridY)
```

From here, we can query for the weather forecast for that grid point.

```bash
WEATHER=$(curl -Ls "https://api.weather.gov/gridpoints/$OFFICE/$X,$Y/forecast")
```

{{< unsafe >}}<details><summary>Show output:</summary>{{</unsafe >}}

```json
{
    "@context": [
        "https://geojson.org/geojson-ld/geojson-context.jsonld",
        {
            "@version": "1.1",
            "wx": "https://api.weather.gov/ontology#",
            "geo": "http://www.opengis.net/ont/geosparql#",
            "unit": "http://codes.wmo.int/common/unit/",
            "@vocab": "https://api.weather.gov/ontology#"
        }
    ],
    "type": "Feature",
    "geometry": {
        "type": "Polygon",
        "coordinates": [
            [
                [
                    -73.6648,
                    42.7172
                ],
                [
                    -73.6602,
                    42.7386
                ],
                [
                    -73.6893,
                    42.742
                ],
                [
                    -73.694,
                    42.720499999999994
                ],
                [
                    -73.6648,
                    42.7172
                ]
            ]
        ]
    },
    "properties": {
        "units": "us",
        "forecastGenerator": "BaselineForecastGenerator",
        "generatedAt": "2025-03-16T19:59:48+00:00",
        "updateTime": "2025-03-16T19:38:29+00:00",
        "validTimes": "2025-03-16T13:00:00+00:00/P8D",
        "elevation": {
            "unitCode": "wmoUnit:m",
            "value": 61.8744
        },
        "periods": [
            {
                "number": 1,
                "name": "This Afternoon",
                "startTime": "2025-03-16T15:00:00-04:00",
                "endTime": "2025-03-16T18:00:00-04:00",
                "isDaytime": true,
                "temperature": 69,
                "temperatureUnit": "F",
                "temperatureTrend": "",
                "probabilityOfPrecipitation": {
                    "unitCode": "wmoUnit:percent",
                    "value": null
                },
                "windSpeed": "22 mph",
                "windDirection": "S",
                "icon": "https://api.weather.gov/icons/land/day/wind_ovc?size=medium",
                "shortForecast": "Cloudy",
                "detailedForecast": "Cloudy, with a high near 69. South wind around 22 mph, with gusts as high as 43 mph. New rainfall amounts less than a tenth of an inch possible."
            },
            {
                "number": 2,
                "name": "Tonight",
                "startTime": "2025-03-16T18:00:00-04:00",
                "endTime": "2025-03-17T06:00:00-04:00",
                "isDaytime": false,
                "temperature": 50,
                "temperatureUnit": "F",
                "temperatureTrend": "",
                "probabilityOfPrecipitation": {
                    "unitCode": "wmoUnit:percent",
                    "value": 100
                },
                "windSpeed": "5 to 21 mph",
                "windDirection": "SW",
                "icon": "https://api.weather.gov/icons/land/night/tsra,100?size=medium",
                "shortForecast": "Showers And Thunderstorms",
                "detailedForecast": "A chance of rain showers before 8pm, then showers and thunderstorms. Cloudy, with a low around 50. Southwest wind 5 to 21 mph, with gusts as high as 44 mph. Chance of precipitation is 100%. New rainfall amounts between three quarters and one inch possible."
            },
            {
                "number": 3,
                "name": "Monday",
                "startTime": "2025-03-17T06:00:00-04:00",
                "endTime": "2025-03-17T18:00:00-04:00",
                "isDaytime": true,
                "temperature": 53,
                "temperatureUnit": "F",
                "temperatureTrend": "",
                "probabilityOfPrecipitation": {
                    "unitCode": "wmoUnit:percent",
                    "value": 60
                },
                "windSpeed": "5 to 12 mph",
                "windDirection": "NW",
                "icon": "https://api.weather.gov/icons/land/day/rain_showers,60/rain_showers,50?size=medium",
                "shortForecast": "Rain Showers Likely",
                "detailedForecast": "Rain showers likely. Cloudy. High near 53, with temperatures falling to around 46 in the afternoon. Northwest wind 5 to 12 mph. Chance of precipitation is 60%. New rainfall amounts between a half and three quarters of an inch possible."
            },
            {
                "number": 4,
                "name": "Monday Night",
                "startTime": "2025-03-17T18:00:00-04:00",
                "endTime": "2025-03-18T06:00:00-04:00",
                "isDaytime": false,
                "temperature": 31,
                "temperatureUnit": "F",
                "temperatureTrend": "",
                "probabilityOfPrecipitation": {
                    "unitCode": "wmoUnit:percent",
                    "value": 30
                },
                "windSpeed": "7 to 10 mph",
                "windDirection": "NW",
                "icon": "https://api.weather.gov/icons/land/night/rain_showers,30/bkn?size=medium",
                "shortForecast": "Chance Rain Showers then Mostly Cloudy",
                "detailedForecast": "A chance of rain showers before 8pm. Mostly cloudy, with a low around 31. Northwest wind 7 to 10 mph. Chance of precipitation is 30%. New rainfall amounts between a tenth and quarter of an inch possible."
            },
            {
                "number": 5,
                "name": "Tuesday",
                "startTime": "2025-03-18T06:00:00-04:00",
                "endTime": "2025-03-18T18:00:00-04:00",
                "isDaytime": true,
                "temperature": 56,
                "temperatureUnit": "F",
                "temperatureTrend": "",
                "probabilityOfPrecipitation": {
                    "unitCode": "wmoUnit:percent",
                    "value": null
                },
                "windSpeed": "7 mph",
                "windDirection": "NW",
                "icon": "https://api.weather.gov/icons/land/day/few?size=medium",
                "shortForecast": "Sunny",
                "detailedForecast": "Sunny, with a high near 56. Northwest wind around 7 mph."
            },
            {
                "number": 6,
                "name": "Tuesday Night",
                "startTime": "2025-03-18T18:00:00-04:00",
                "endTime": "2025-03-19T06:00:00-04:00",
                "isDaytime": false,
                "temperature": 35,
                "temperatureUnit": "F",
                "temperatureTrend": "",
                "probabilityOfPrecipitation": {
                    "unitCode": "wmoUnit:percent",
                    "value": null
                },
                "windSpeed": "1 to 5 mph",
                "windDirection": "NE",
                "icon": "https://api.weather.gov/icons/land/night/few?size=medium",
                "shortForecast": "Mostly Clear",
                "detailedForecast": "Mostly clear, with a low around 35."
            },
            {
                "number": 7,
                "name": "Wednesday",
                "startTime": "2025-03-19T06:00:00-04:00",
                "endTime": "2025-03-19T18:00:00-04:00",
                "isDaytime": true,
                "temperature": 65,
                "temperatureUnit": "F",
                "temperatureTrend": "",
                "probabilityOfPrecipitation": {
                    "unitCode": "wmoUnit:percent",
                    "value": null
                },
                "windSpeed": "2 to 9 mph",
                "windDirection": "SE",
                "icon": "https://api.weather.gov/icons/land/day/sct?size=medium",
                "shortForecast": "Mostly Sunny",
                "detailedForecast": "Mostly sunny, with a high near 65."
            },
            {
                "number": 8,
                "name": "Wednesday Night",
                "startTime": "2025-03-19T18:00:00-04:00",
                "endTime": "2025-03-20T06:00:00-04:00",
                "isDaytime": false,
                "temperature": 45,
                "temperatureUnit": "F",
                "temperatureTrend": "",
                "probabilityOfPrecipitation": {
                    "unitCode": "wmoUnit:percent",
                    "value": null
                },
                "windSpeed": "9 mph",
                "windDirection": "SE",
                "icon": "https://api.weather.gov/icons/land/night/bkn?size=medium",
                "shortForecast": "Mostly Cloudy",
                "detailedForecast": "Mostly cloudy, with a low around 45."
            },
            {
                "number": 9,
                "name": "Thursday",
                "startTime": "2025-03-20T06:00:00-04:00",
                "endTime": "2025-03-20T18:00:00-04:00",
                "isDaytime": true,
                "temperature": 61,
                "temperatureUnit": "F",
                "temperatureTrend": "",
                "probabilityOfPrecipitation": {
                    "unitCode": "wmoUnit:percent",
                    "value": 50
                },
                "windSpeed": "8 to 14 mph",
                "windDirection": "S",
                "icon": "https://api.weather.gov/icons/land/day/bkn/rain_showers,50?size=medium",
                "shortForecast": "Mostly Cloudy then Chance Rain Showers",
                "detailedForecast": "A chance of rain showers after 2pm. Mostly cloudy, with a high near 61. Chance of precipitation is 50%."
            },
            {
                "number": 10,
                "name": "Thursday Night",
                "startTime": "2025-03-20T18:00:00-04:00",
                "endTime": "2025-03-21T06:00:00-04:00",
                "isDaytime": false,
                "temperature": 33,
                "temperatureUnit": "F",
                "temperatureTrend": "",
                "probabilityOfPrecipitation": {
                    "unitCode": "wmoUnit:percent",
                    "value": 70
                },
                "windSpeed": "8 to 12 mph",
                "windDirection": "SW",
                "icon": "https://api.weather.gov/icons/land/night/rain_showers,70/snow,70?size=medium",
                "shortForecast": "Rain Showers Likely then Chance Rain And Snow Showers",
                "detailedForecast": "Rain showers likely before 2am, then a chance of rain and snow showers. Mostly cloudy, with a low around 33. Chance of precipitation is 70%."
            },
            {
                "number": 11,
                "name": "Friday",
                "startTime": "2025-03-21T06:00:00-04:00",
                "endTime": "2025-03-21T18:00:00-04:00",
                "isDaytime": true,
                "temperature": 41,
                "temperatureUnit": "F",
                "temperatureTrend": "",
                "probabilityOfPrecipitation": {
                    "unitCode": "wmoUnit:percent",
                    "value": 50
                },
                "windSpeed": "12 to 17 mph",
                "windDirection": "NW",
                "icon": "https://api.weather.gov/icons/land/day/snow,50/snow,30?size=medium",
                "shortForecast": "Chance Rain And Snow Showers",
                "detailedForecast": "A chance of rain and snow showers. Partly sunny, with a high near 41. Chance of precipitation is 50%."
            },
            {
                "number": 12,
                "name": "Friday Night",
                "startTime": "2025-03-21T18:00:00-04:00",
                "endTime": "2025-03-22T06:00:00-04:00",
                "isDaytime": false,
                "temperature": 30,
                "temperatureUnit": "F",
                "temperatureTrend": "",
                "probabilityOfPrecipitation": {
                    "unitCode": "wmoUnit:percent",
                    "value": null
                },
                "windSpeed": "9 to 16 mph",
                "windDirection": "NW",
                "icon": "https://api.weather.gov/icons/land/night/snow/sct?size=medium",
                "shortForecast": "Slight Chance Snow Showers then Partly Cloudy",
                "detailedForecast": "A slight chance of snow showers before 8pm. Partly cloudy, with a low around 30."
            },
            {
                "number": 13,
                "name": "Saturday",
                "startTime": "2025-03-22T06:00:00-04:00",
                "endTime": "2025-03-22T18:00:00-04:00",
                "isDaytime": true,
                "temperature": 52,
                "temperatureUnit": "F",
                "temperatureTrend": "",
                "probabilityOfPrecipitation": {
                    "unitCode": "wmoUnit:percent",
                    "value": null
                },
                "windSpeed": "9 to 13 mph",
                "windDirection": "NW",
                "icon": "https://api.weather.gov/icons/land/day/sct?size=medium",
                "shortForecast": "Mostly Sunny",
                "detailedForecast": "Mostly sunny, with a high near 52."
            },
            {
                "number": 14,
                "name": "Saturday Night",
                "startTime": "2025-03-22T18:00:00-04:00",
                "endTime": "2025-03-23T06:00:00-04:00",
                "isDaytime": false,
                "temperature": 34,
                "temperatureUnit": "F",
                "temperatureTrend": "",
                "probabilityOfPrecipitation": {
                    "unitCode": "wmoUnit:percent",
                    "value": null
                },
                "windSpeed": "3 to 9 mph",
                "windDirection": "NW",
                "icon": "https://api.weather.gov/icons/land/night/bkn?size=medium",
                "shortForecast": "Mostly Cloudy",
                "detailedForecast": "Mostly cloudy, with a low around 34."
            }
        ]
    }
}
```

{{< unsafe >}}</details><br/>{{</unsafe >}}

The National Weather Service packs in so much weather information in just one API call! My favorite part is that they have a `detailedForecast` field which provides a nice human-readable description of the weather.

I don't know about you, but at any given time, I'm mostly curious about today and tomorrow's weather. Unless I'm planning a trip or need to be aware of an extreme weather event, the day's forecast mostly influences the clothes I wear.

The final part of this script is to grab the next three "periods" and display its `detailedForecast` field.

```bash
for i in 0 1 2; do
    echo "$WEATHER" | jq .properties.periods[$i] | jq -r '
  "\(.name)
  \(.detailedForecast)
  " 
'
done
```

Instead of having to read an entire JSON message to get the weather, we now have a description of the forecast coming up. 

```
This Afternoon
  Cloudy, with a high near 69. South wind around 22 mph, with gusts as high as 43 mph. New rainfall amounts less than a tenth of an inch possible.
  
Tonight
  A chance of rain showers before 8pm, then showers and thunderstorms. Cloudy, with a low around 50. Southwest wind 5 to 21 mph, with gusts as high as 44 mph. Chance of precipitation is 100%. New rainfall amounts between three quarters and one inch possible.
  
Monday
  Rain showers likely. Cloudy. High near 53, with temperatures falling to around 46 in the afternoon. Northwest wind 5 to 12 mph. Chance of precipitation is 60%. New rainfall amounts between a half and three quarters of an inch possible.

```

Look how short and sweet that output is! With that, we have all the steps needed in our script to grab the upcoming forecast using the NWS API. I created an alias called `myweather` so that I don't have to memorize the latitude or longitude of where I live.

```bash
alias myweather='usweather 42.7289, -73.6915'
```

Here is the script that I call `usweather` in its entirety. I placed it in `~/.local/bin`. 

```bash
#!/bin/sh
# Script to query the US National Weather Forecast Office (WFO)

set -o errexit
set -o nounset

show_usage() {
    echo "Usage: usweather [lat] [lon]"
    exit 1
}

# Check Argument Count
if [ "$#" -ne 2 ]; then
    show_usage
fi

if ! command -v jq &> /dev/null; then
    echo "jq is not installed"
    exit 1
fi

# We need to figure out WFO specific parameters
POINTS=$(curl -Ls "https://api.weather.gov/points/$1,$2")
OFFICE=$(echo $POINTS | jq -r .properties.gridId)
X=$(echo $POINTS | jq .properties.gridX)
Y=$(echo $POINTS | jq .properties.gridY)

if [ "$OFFICE" = "null" ] || [ "$X" = "null" ] || [ "$Y" = "null" ]; then
	echo -e "Error:\n $POINTS"
	exit 1
fi

WEATHER=$(curl -Ls "https://api.weather.gov/gridpoints/$OFFICE/$X,$Y/forecast")

# Provide the detailed forecast for the next three weather periods
for i in 0 1 2; do
    echo "$WEATHER" | jq .properties.periods[$i] | jq -r '
  "\(.name)
  \(.detailedForecast)
  " 
'
done

```

